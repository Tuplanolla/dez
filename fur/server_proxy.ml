open Polynomial_types
open Component_types
open Thrift
open Util

module Log = (val Logs.src_log (Logs.Src.create "maniunfold.fur"))

let start ?(addr="127.0.0.1") ?(port=8191) () =
  (** TODO Do we need this exclusion for signals? *)
  let mutex = Mutex.create () in
  let atomically f =
    bracket
    ~acquire:(fun () -> Mutex.lock mutex)
    ~release:(fun () -> Mutex.unlock mutex)
    f in
  let on = ref true in
  Log.info (fun m -> m "Connecting to %s." addr);
  let trans = new TSocket.t addr port in
  let proto = new TBinaryProtocol.t trans in
  proto#getTransport#opn;
  let id = new identity in
  id#set_name "fur";
  id#write proto;
  proto#getTransport#flush;
  Log.info (fun m -> m "Sent identification.");
  while atomically (fun () -> !on) do try
    let req = read_request proto in
    Log.info (fun m -> m "Received request.");
    match req#grab_type with
    | Request_type.EVAL ->
        let poly = req#grab_data#grab_eval in
        let value = Server.crunch poly#grab_coeffs poly#grab_point in
        Unix.sleep 1;
        let res = new response in
        res#set_value value;
        res#write proto;
        proto#getTransport#flush;
        Log.info (fun m -> m "Sent response.")
    | Request_type.EXIT ->
        atomically (fun () -> on := false);
        Log.info (fun m -> m "Stopped serving the people.")
  with
  | Def_sys.Signal i when i = Sys.sigint ->
      atomically (fun () -> on := false)
  done;
  proto#getTransport#close
