open Polynomial_types
open Thrift

(** Pretend we are writing Haskell. *)
(* val bracket : acquire:(unit -> 'a) -> ('a -> 'b) -> release:('a -> unit) -> 'b *)
let bracket ~acquire work ~release =
  let a = acquire () in
  let w = try work a with
    | e -> release a ;
      raise e in
  release a ;
  w

module TReusableServerSocket =
  struct
    (** We need this subclass to set `SO_REUSEADDR`. *)
    class t port =
      object
        inherit TServerSocket.t port
        method listen =
          let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
          sock <- Some s ;
          Unix.setsockopt s SO_REUSEADDR true ;
          Unix.bind s (Unix.ADDR_INET (Unix.inet_addr_any, port)) ;
          Unix.listen s 256
      end
  end

(** Listen for connections,
    start `fur` process, accept connection from `fur`,
    start `scales` process, accept connection from `scales`,
    get message from `scales`, either:
    forward message to `fur`, get message from `fur`,
    forward message to `scales`, repeat; or:
    stop processes, exit. *)
let main () =
  bracket
    ~acquire:begin fun () ->
      let strans : Transport.server_t = new TReusableServerSocket.t 9092 in
      strans
    end
    ~release:begin fun strans ->
      strans#close
    end
    (* TODO Error recovery for when Python chokes. *)
    begin fun strans ->
      strans#listen ;

      let cwd = Sys.getcwd () in
      Sys.chdir "../scales" ;
      (* let exitcode = Sys.command "python3 client_proxy.py" in *)
      let py = "python3" in
      let pid = Unix.create_process py [|py; "client_proxy.py"|]
        Unix.stdin Unix.stdout Unix.stderr in
      Sys.chdir cwd ;

      let trans = strans#accept in
      let proto = new TBinaryProtocol.t trans in
      let req = read_request proto in
      let value = Hashtbl.fold
        (fun i a y -> y +. a *. req#grab_point ** Int32.to_float i)
        req#grab_coeffs 0. in
      let res = new response in
      res#set_value value ;
      res#write proto ;
      proto#getTransport#flush ;
      proto#getTransport#close
    end
