open Component_types
open Polynomial_types
open Thrift
open Util

module Log = (val Logs.src_log (Logs.Src.create "maniunfold.ape"))

type state =
  | Idle
  | Working

type component = Protocol.t * state

let broker_port = 8191

let start ?(port=broker_port) () =
  bracket
  ~acquire:(fun () -> new TThreadedServerSocket.t port)
  ~release:(fun strans -> strans#close)
  begin fun strans ->
    let mutex = Mutex.create () in
    let atomically f =
      bracket
      ~acquire:(fun () -> Mutex.lock mutex)
      ~release:(fun () -> Mutex.unlock mutex)
      f in
    let comps : (string, component) Hashtbl.t = Hashtbl.create 0 in
    let on = ref true in
    strans#listen;
    Log.debug begin fun m ->
      m "Started listening for connections on thread %d."
      (Thread.id (Thread.self ()))
    end;
    while atomically (fun () -> !on) do try
      (** TODO This kind of scheduling is dumb.

          Client-like components should be unblocked and
          have their threads blocked on reads,
          while server-like components should be blocked on reads and
          have their threads free or unallocated.

          When client-like components send data and
          unblock the corresponding threads,
          those threads should fire the appropriate server-like components and
          block them on writes (and the threads on reads).

          In short, allocate threads for blocking contexts, not components.
          Note that an unidentified accepted connection
          is also a blocking context. *)
      let thread = Thread.create begin fun trans ->
        let proto = new TBinaryProtocol.t trans in
        let id = read_identity proto in
        let name = id#grab_name in
        Log.debug begin fun m ->
          m "Identified thread %d as %s." (Thread.id (Thread.self ())) name
        end;
        (** TODO Handle duplicate keys.
            Perhaps allow duplicate keys,
            but treat duplicate components as indistinguishable. *)
        match name with
        | "fur" ->
            atomically begin fun () ->
              Hashtbl.add comps name (proto, Idle)
            end
        | "scales" ->
            atomically begin fun () ->
              Hashtbl.add comps name (proto, Idle)
            end;
            (** TODO There must be a better way to handle exiting. *)
            let hard_on = ref true in
            while atomically (fun () -> !on && !hard_on) do try
              let req = read_request proto in
              Log.info (fun m -> m "Received request.");
              match req#grab_type with
              | Request_type.EVAL ->
                  begin match atomically begin fun () ->
                    Hashtbl.find_opt comps "fur"
                  end with
                  | Some (sproto, Idle) ->
                      (** TODO Change state here. *)
                      req#write sproto;
                      sproto#getTransport#flush;
                      let res = read_response sproto in
                      res#write proto;
                      proto#getTransport#flush;
                      Log.info (fun m -> m "Sent response.")
                  (** TODO Handle missing or busy server. *)
                  | _ -> ()
                  end
              | Request_type.EXIT -> hard_on := false
              (** TODO On failure... *)
              (* atomically begin fun () ->
                match !names with
                | None -> ()
                | Some name -> Hashtbl.remove comps name
              end *)
            with
            | Def_sys.Signal i when i = Sys.sigint ->
                atomically (fun () -> on := false)
            done;
            atomically begin fun () ->
              Hashtbl.remove comps name
            end;
            Log.debug (fun m -> m "Ended thread %d."
              (Thread.id (Thread.self ())))
        | name -> raise (Invalid_argument name)
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
    end;
    (** TODO Graceful full shutdown. *)
    match atomically begin fun () ->
      Hashtbl.find_opt comps "fur"
    end with
    | Some (sproto, Idle) ->
        let req = new request in
        req#set_type Request_type.EXIT;
        req#set_data new request_data;
        req#write sproto;
        sproto#getTransport#flush;
        Log.info (fun m -> m "Shut down leftover server.")
    (** TODO Handle missing or busy server. *)
    | _ -> ()
  end
