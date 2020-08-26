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

let start () =
  bracket
    ~acquire:begin fun () ->
      (** This is the only unregistered port
          that is both prime and has a trivial binary representation. *)
      new TThreadedServerSocket.t 8191
    end
    ~release:begin fun strans ->
      strans#close
    end
    begin fun strans ->
      Log.info (fun m -> m "Process is listening.");
      strans#listen;
      let mutex = Mutex.create () in
      let atomically f =
        Mutex.lock mutex;
        f ();
        Mutex.unlock mutex in
      let tbl = Hashtbl.create 0 in
      (** TODO Now pool connections here and start brokering! *)
      while true do
        let thread = Thread.create begin fun trans ->
          let proto = new TBinaryProtocol.t (trans :> Transport.t) in
          let id = read_identity proto in
          (** TODO Handle duplicate keys. *)
          atomically begin fun () ->
            Hashtbl.add tbl id#grab_name proto
          end;
          match id#grab_name with
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
          | name -> raise (Invalid_argument name);
          atomically begin fun () ->
            Hashtbl.remove tbl id#grab_name;
          end
        end
        strans#accept in
        Log.debug (fun m -> m "Started subprocess %d." (Thread.id thread))
      done
      (** TODO Graceful exit. *)
    end
