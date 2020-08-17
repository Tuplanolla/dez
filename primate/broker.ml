let () =
  (** Listen for connections,
      start `fur` process, accept connection from `fur`,
      start `scales` process, accept connection from `scales`,
      get message from `scales`, either:
      forward message to `fur`, get message from `fur`,
      forward message to `scales`, repeat; or:
      stop processes, exit. *)
  print_endline "magic"

open Thrift
open Messages_types

let t1 () =
  let trans : Transport.t = new TSocket.t "localhost" 9092 in
  let proto : Protocol.t = new TBinaryProtocol.t trans in
  proto#getTransport#opn ;
  proto#writeI32 42l ;
  proto#writeI32 13l ;
  proto#getTransport#flush ;
  let buf = Bytes.create 4 in
  let _ = proto#getTransport#read buf 0 4 in
  proto#getTransport#close ;
  let coeffs = Hashtbl.create 2 in
  Hashtbl.add coeffs 42. 0l ;
  Hashtbl.add coeffs 13. 2l ;
  print_endline (Bytes.to_string buf)

(** We need this subclass to set `SO_REUSEADDR`. *)
class custom_server_t port =
  object
    inherit TServerSocket.t port
    method get_sock =
      sock
    method grab_sock =
      match sock with
      | None -> raise (Field_empty "sock")
      | Some sock -> sock
    method listen =
      let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
      sock <- Some s ;
      Unix.setsockopt s SO_REUSEADDR true ;
      Unix.bind s (Unix.ADDR_INET (Unix.inet_addr_any, port)) ;
      Unix.listen s 256
  end

let main () =
  (* let strans : Transport.server_t = new TServerSocket.t 9092 in *)
  let strans : custom_server_t = new custom_server_t 9092 in
  strans#listen ;

  let cwd = Sys.getcwd () in
  Sys.chdir "../scales" ;
  (* let exitcode = Sys.command "python3 client-proxy.py" in *)
  let py = "python3" in
  let pid = Unix.create_process py [|py; "client-proxy.py"|]
    Unix.stdin Unix.stdout Unix.stderr in
  Sys.chdir cwd ;

  let trans = strans#accept in
  let proto = new TBinaryProtocol.t trans in
  let coeffs0 = proto#readI32 in
  let coeffs1 = proto#readI32 in
  let point = 7l in
  let value = Int32.add coeffs0 (Int32.mul coeffs1 (Int32.mul point point)) in
  proto#writeI32 value ;
  proto#getTransport#flush ;
  let req = read_request proto in
  let value = Hashtbl.fold
    (fun i a y -> y +. a *. req#grab_point ** Int32.to_float i)
    req#grab_coeffs 0. in
  let res = new response in
  res#set_value value ;
  res#write proto ;
  proto#getTransport#flush ;
  proto#getTransport#close ;
  strans#close (* TODO Not exception-safe. *)

let () =
  main ()
