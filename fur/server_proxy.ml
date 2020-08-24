open Polynomial_types
open Thrift

module Log = (val Logs.src_log (Logs.Src.create "maniunfold.fur"))

let start () =
  Log.info (fun m -> m "Connecting to %s." "localhorse");
  trans = TTransport.TBufferedTransport(TSocket.TSocket('127.0.0.1', 9092))
  proto = TBinaryProtocol.TBinaryProtocol(trans)
  proto.trans.open()
  req = request(coeffs={0: 42.0, 2: 13.0}, point=7.0)
  req.write(proto)
  proto.trans.flush()
  res = response()
  res.read(proto)
  proto.trans.close()
  logger.info('Work is done.')
  print(str(res))
  Log.info (fun m -> m "Server started %d." pid);
  let trans = strans#accept in
  let proto = new TBinaryProtocol.t trans in
  let req = read_request proto in
  let value = Hashtbl.fold
    (fun i a y -> y +. a *. req#grab_point ** Int32.to_float i)
    req#grab_coeffs 0. in
  let res = new response in
  res#set_value value;
  res#write proto;
  proto#getTransport#flush;
  proto#getTransport#close
