open Polynomial_types
open Thrift
open Util

module TReusableServerSocket =
  struct
    (** We need this subclass to set `SO_REUSEADDR`. *)
    class t port =
      object
        inherit TServerSocket.t port
        method listen =
          let s = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
          sock <- Some s ;
          Unix.setsockopt s Unix.SO_REUSEADDR true ;
          Unix.bind s (Unix.ADDR_INET (Unix.inet_addr_any, port)) ;
          Unix.listen s 256
      end
  end

(*
let och = open_out "/tmp/primate.log" in
let f = Format.formatter_of_out_channel och in
Logs.set_reporter (Logs.format_reporter ~app:f ~dst:f ()) ;
Logs.set_level (Some Logs.Debug)

module Log = (val Logs.src_log (Logs.Src.create "primate"))
Logs.debug (fun f -> f "Good!")

close_out och
*)

(** Listen for connections,
    start `fur` process, accept connection from `fur`,
    start `scales` process, accept connection from `scales`,
    get message from `scales`, either:
    forward message to `fur`, get message from `fur`,
    forward message to `scales`, repeat; or:
    stop processes, exit. *)
let start () =
  bracket
    ~acquire:begin fun () ->
      let strans : Transport.server_t = new TReusableServerSocket.t 9092 in
      strans
    end
    ~release:begin fun strans ->
      strans#close
    end
    begin fun strans ->
      print_endline ("Process " ^ string_of_int (Unix.getpid ()) ^
        " is listening.") ;
      strans#listen ;

      bracket
        ~acquire:begin fun () ->
          (* TODO Cwd is a resource. *)
          let cwd = Sys.getcwd () in
          Sys.chdir "../scales" ;
          (* let exitcode = Sys.command "python3 main.py" in *)
          let py = "python3" in
          let pid = Unix.create_process py [|py; "main.py"|]
            Unix.stdin Unix.stdout Unix.stderr in
          Sys.chdir cwd ;
          print_endline ("Process " ^ string_of_int (Unix.getpid ()) ^
            " started subprocess " ^ string_of_int pid ^ ".") ;
          pid
        end
        ~release:begin fun pid ->
          (* Unix.kill pid Sys.sigterm ;
          print_endline ("Process " ^ string_of_int (Unix.getpid ()) ^
            " killed subprocess " ^ string_of_int pid ^ ".") ;
          let i, s = Unix.waitpid [] pid in *)
          ()
        end
        begin fun pid ->
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
    end
