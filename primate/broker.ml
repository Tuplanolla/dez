open Component_types
open Polynomial_types
open Thrift
open Util

module Log = (val Logs.src_log (Logs.Src.create "maniunfold.primate"))

(** We need to extend [Transport]
    with capabilities for preemptive multitasking.
    We also add [SO_REUSEADDR] to the socket options. *)

module TThreadedSocket =
  struct
    class t host port =
      let open Unix in
      let open ThreadUnix in
      object
        inherit TSocket.t host port
        method isOpen = chans != None
        method opn =
          try
            let addr = (gethostbyname host).h_addr_list.(0) in
            chans <- Some (open_connection (ADDR_INET (addr, port)))
          with
          | Unix_error (e, fn, _) ->
              raise begin
                Transport.E begin
                  Transport.NOT_OPEN,
                  "TThreadedSocket: Could not connect to " ^
                  host ^ ":" ^ string_of_int port ^
                  " because: " ^ fn ^ ": " ^ error_message e
                end
              end
          | _ ->
              raise begin
                Transport.E begin
                  Transport.NOT_OPEN,
                  "TThreadedSocket: Could not connect to " ^
                  host ^ ":" ^ string_of_int port
                end
              end
        method close =
          match chans with
          | None -> ()
          | Some (inc, out) ->
              shutdown_connection inc;
              close_in inc;
              chans <- None
        method read buf off len =
          match chans with
          | None ->
              raise begin
                Transport.E begin
                  Transport.NOT_OPEN,
                  "TThreadedSocket: Socket not open"
                end
              end
          | Some (i, o) ->
              try
                really_input i buf off len;
                len
              with
              | Unix_error (e, fn, _) ->
                  raise begin
                    Transport.E begin
                      Transport.UNKNOWN,
                      "TThreadedSocket: Could not read " ^ string_of_int len ^
                      " bytes from " ^ host ^ ":" ^ string_of_int port ^
                      " because: " ^ fn ^ ": " ^ error_message e
                    end
                  end
              | _ ->
                  raise begin
                    Transport.E begin
                      Transport.UNKNOWN,
                      "TThreadedSocket: Could not read " ^ string_of_int len ^
                      " bytes from " ^ host ^ ":" ^ string_of_int port
                    end
                  end
        method write buf off len =
          match chans with
          | None ->
              raise begin
                Transport.E begin
                  Transport.NOT_OPEN,
                  "TThreadedSocket: Socket not open"
                end
              end
          | Some (i, o) -> output o buf off len
        method write_string buf off len =
          match chans with
          | None ->
              raise begin
                Transport.E begin
                  Transport.NOT_OPEN,
                  "TThreadedSocket: Socket not open"
                end
              end
          | Some (i, o) -> output_substring o buf off len
        method flush =
          match chans with
          | None ->
              raise begin
                Transport.E begin
                  Transport.NOT_OPEN,
                  "TThreadedSocket: Socket not open"
                end
              end
          | Some (i, o) -> flush o
      end
  end

module TThreadedServerSocket =
  struct
    class t port =
      let open Unix in
      let open ThreadUnix in
      object
        inherit TServerSocket.t port
        method listen =
          let s = socket PF_INET SOCK_STREAM 0 in
          sock <- Some s;
          setsockopt s SO_REUSEADDR true;
          bind s (ADDR_INET (inet_addr_any, port));
          listen s 256
        method close =
          match sock with
          | None -> ()
          | Some s ->
              shutdown s SHUTDOWN_ALL;
              close s;
              sock <- None
        method acceptImpl =
          match sock with
          | None ->
              raise begin
                Transport.E begin
                  Transport.NOT_OPEN,
                  "TThreadedServerSocket: Not listening but tried to accept"
                end
              end
          | Some s ->
              let fd, _ = accept s in
              new TChannelTransport.t begin
                in_channel_of_descr fd,
                out_channel_of_descr fd
              end
      end
  end

type state =
  | Idle
  | Working

type component = Thread.t * Protocol.t * state

let broker_port = 8191

let start () =
  bracket
  ~acquire:(fun () -> new TThreadedServerSocket.t broker_port)
  ~release:(fun strans -> strans#close)
  begin fun strans ->
    let mutex = Mutex.create () in
    let atomically f =
      bracket
      ~acquire:(fun () -> Mutex.lock mutex)
      ~release:(fun () -> Mutex.unlock mutex)
      f in
    let comps = Hashtbl.create 0 in
    let on = ref true in
    strans#listen;
    Log.debug begin fun m ->
      m "Started listening for connections on thread %d."
      (Thread.id (Thread.self ()))
    end;
    while atomically (fun () -> !on) do
      try
      (** TODO This kind of scheduling is dumb.

          Client-like components should be unblocked and
          have their threads blocked on reads,
          while server-like components should be blocked on reads and
          have their threads free or unallocated.

          When client-like components send data and
          unblock the corresponding threads,
          those threads should fire the appropriate server-like components and
          block them on writes (and the threads on reads).

          In short, allocate threads for blocking contexts, not components. *)
      let thread = Thread.create begin fun trans ->
        bracket
        ~acquire:(fun () -> ref None)
        ~release:begin fun names ->
          atomically begin fun () ->
            match !names with
            | None -> ()
            | Some name -> Hashtbl.remove comps name
          end
        end
        begin fun names ->
          let proto = new TBinaryProtocol.t trans in
          let id = read_identity proto in
          let name = id#grab_name in
          (** TODO Handle duplicate keys.
              Perhaps allow duplicate keys,
              but treat duplicate components as indistinguishable. *)
          match name with
          | "fur" ->
              (** TODO Do not allocate a thread here. *)
              while atomically (fun () -> !on) do
                Thread.delay 0.1
              done
          | "scales" ->
              (** TODO Repeat this process on this thread. *)
              atomically begin fun () ->
                Hashtbl.add comps name (Thread.self (), proto, Idle);
                names := Some name
              end;
              Log.debug (fun m -> m "Identified the animal.");
              let req = read_request proto in
              let value = Hashtbl.fold
                (fun i a y -> y +. a *. req#grab_point ** Int32.to_float i)
                req#grab_coeffs 0. in
              (** TODO Stop sleeping all the time. *)
              Unix.sleep 2;
              let res = new response in
              res#set_value value;
              res#write proto;
              proto#getTransport#flush;
              proto#getTransport#close;
              Log.debug (fun m -> m "Ended thread %d."
                (Thread.id (Thread.self ())))
          | name -> raise (Invalid_argument name)
        end
      end
      strans#accept in
      Log.debug begin fun m ->
        m "Accepted a connection on thread %d." (Thread.id thread)
      end
    with
    | Def_sys.Signal i when i = Sys.sigint ->
        atomically (fun () -> on := false)
    done;
    Log.debug begin fun m ->
      m "Stopped listening for connections on thread %d."
      (Thread.id (Thread.self ()))
    end
  end
