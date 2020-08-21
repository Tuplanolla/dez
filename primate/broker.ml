open Polynomial_types
open Thrift
open Util

module Log = (val Logs.src_log (Logs.Src.create "maniunfold.primate"))

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
      Log.info (fun m -> m "Process %d is listening." (Unix.getpid ())) ;
      strans#listen ;

      bracket
        ~acquire:begin fun () ->
          bracket
            ~acquire:begin fun () ->
              let cwd = Sys.getcwd () in
              Sys.chdir "../scales" ;
              cwd
            end
            ~release:Sys.chdir
            begin fun _ ->
              let prog = "python3" in
              let args = [|prog; "main.py"|] in
              Unix.create_process prog args Unix.stdin Unix.stdout Unix.stderr
            end
        end
        ~release:begin fun pid ->
          (** We can apply this in case of a crisis. *)
          (* Unix.kill pid Sys.sigterm ; *)
          let i, w = Unix.waitpid [] pid in
          match w with
          | Unix.WEXITED _ ->
            Log.info (fun m -> m "Process %d terminated subprocess %d (WEXIT)."
              (Unix.getpid ()) pid)
          | Unix.WSIGNALED _ ->
            Log.info (fun m -> m "Process %d terminated subprocess %d (WSIG)."
              (Unix.getpid ()) pid)
          | Unix.WSTOPPED _ ->
            Log.info (fun m -> m "Process %d terminated subprocess %d (WSTOP)."
              (Unix.getpid ()) pid)
        end
        begin fun pid ->
          Log.info (fun m -> m "Process %d started subprocess %d."
            (Unix.getpid ()) pid) ;
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
