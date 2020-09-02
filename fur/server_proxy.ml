open Polynomial_types
open Component_types
open Thrift
open Util

module Log = (val Logs.src_log (Logs.Src.create "maniunfold.fur"))

let broker_port = 8191

let start () =
  let mutex = Mutex.create () in
  let atomically f =
    bracket
    ~acquire:(fun () -> Mutex.lock mutex)
    ~release:(fun () -> Mutex.unlock mutex)
    f in
  let on = ref true in
  Log.info (fun m -> m "Connecting to %s." "localhorse");
  let trans = new TSocket.t "localhost" broker_port in
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
    (** TODO Call the extracted server code here. *)
    let value = Hashtbl.fold
      (fun i a y -> y +. a *. req#grab_point ** Int32.to_float i)
      req#grab_coeffs 0. in
    Unix.sleep 1;
    let res = new response in
    res#set_value value;
    res#write proto;
    proto#getTransport#flush;
    Log.info (fun m -> m "Sent response.")
  with
  | Def_sys.Signal i when i = Sys.sigint ->
      atomically (fun () -> on := false)
  | Thrift.Transport.E _ ->
      atomically (fun () -> on := false)
  done;
  proto#getTransport#close
