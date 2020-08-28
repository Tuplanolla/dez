open Component_types
open Polynomial_types
open Thrift
open Util

module Log = (val Logs.src_log (Logs.Src.create "maniunfold.primate"))

(** We need to extend [Transport]
    with capabilities for preemptive multitasking.
    We also add [SO_REUSEADDR] to the socket options.
    As you can see, object-oriented programming was a mistake. *)

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
            let addr = (let {h_addr_list=x} = gethostbyname host in x.(0)) in
              chans <- Some (open_connection (ADDR_INET (addr, port)))
          with
          | Unix_error (e, fn, _) -> raise (Transport.E (Transport.NOT_OPEN, ("TSocket: Could not connect to "^host^":"^(string_of_int port)^" because: "^fn^":"^(error_message e))))
          | _ -> raise (Transport.E (Transport.NOT_OPEN, ("TSocket: Could not connect to "^host^":"^(string_of_int port))))
        method close =
          match chans with
          | None -> ()
          | Some (inc, out) -> (shutdown_connection inc;
                              close_in inc;
                              chans <- None)
        method read buf off len = match chans with
          | None -> raise (Transport.E (Transport.NOT_OPEN, "TSocket: Socket not open"))
          | Some (i, o) ->
              try
                really_input i buf off len; len
              with
              | Unix_error (e, fn, _) -> raise (Transport.E (Transport.UNKNOWN, ("TSocket: Could not read "^(string_of_int len)^" from "^host^":"^(string_of_int port)^" because: "^fn^":"^(error_message e))))
              | _ -> raise (Transport.E (Transport.UNKNOWN, ("TSocket: Could not read "^(string_of_int len)^" from "^host^":"^(string_of_int port))))
        method write buf off len =
          match chans with
          | None -> raise (Transport.E (Transport.NOT_OPEN, "TSocket: Socket not open"))
          | Some (i, o) -> output o buf off len
        method write_string buf off len =
          match chans with
          | None -> raise (Transport.E (Transport.NOT_OPEN, "TSocket: Socket not open"))
          | Some (i, o) -> output_substring o buf off len
        method flush =
          match chans with
          | None -> raise (Transport.E (Transport.NOT_OPEN, "TSocket: Socket not open"))
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
          | None -> raise
              (Transport.E (Transport.NOT_OPEN, "TServerSocket: Not listening but tried to accept"))
          | Some s ->
              let fd, _ = accept s in
              new TChannelTransport.t
              (in_channel_of_descr fd, out_channel_of_descr fd)
      end
  end

(** We cannot use [TThreadedServer] here,
    because threads get blocked on system calls. *)

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
    let protos = Hashtbl.create 0 in
    let on = ref true in
    strans#listen;
    Log.debug begin fun m ->
      m "Started listening for connections on thread %d."
      (Thread.id (Thread.self ()))
    end;
    while atomically (fun () -> !on) do
      try
      let thread = Thread.create begin fun trans ->
        bracket
        ~acquire:begin fun () ->
          ref None
        end
        ~release:begin fun names ->
          atomically begin fun () ->
            match !names with
            | None -> ()
            | Some name -> Hashtbl.remove protos name
          end
        end
        begin fun names ->
          let proto = new TBinaryProtocol.t trans in
          let id = read_identity proto in
          let name = id#grab_name in
          (** TODO Handle duplicate keys. *)
          atomically begin fun () ->
            Hashtbl.add protos name proto;
            names := Some name
          end;
          match name with
          | "fur" -> raise (Invalid_argument "Not supported yet")
          | "scales" ->
              Log.debug (fun m -> m "Identified the animal.");
              let req = read_request proto in
              let value = Hashtbl.fold
                (fun i a y -> y +. a *. req#grab_point ** Int32.to_float i)
                req#grab_coeffs 0. in
              (** TODO Stop sleeping all the time. *)
              Unix.sleep 1;
              let res = new response in
              res#set_value value;
              res#write proto;
              proto#getTransport#flush;
              proto#getTransport#close;
              Log.debug (fun m -> m "Ended subprocess %d."
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
