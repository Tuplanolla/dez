open Polynomial_types
open Thrift

module Log = (val Logs.src_log (Logs.Src.create "maniunfold.fur"))

let start () =
  Log.info (fun m -> m "Connecting to %s." "localhorse");
  let trans = new TSocket.t "localhost" 9092 in
  let proto = new TBinaryProtocol.t trans in
  proto#getTransport#opn;
  let req = read_request proto in
  (** TODO Call the extracted server code here. *)
  let value = Hashtbl.fold
    (fun i a y -> y +. a *. req#grab_point ** Int32.to_float i)
    req#grab_coeffs 0. in
  let res = new response in
  res#set_value value;
  res#write proto;
  proto#getTransport#flush;
  proto#getTransport#close
