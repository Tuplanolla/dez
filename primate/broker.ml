open Polynomial_types
open Thrift
open Util

module Log = (val Logs.src_log (Logs.Src.create "maniunfold.primate"))

module TReusableServerSocket =
  struct
    (** We need this subclass to set [SO_REUSEADDR] and
        call [close] without calling [shutdown]. *)
    class t port =
      let open Unix in
      object
        inherit TServerSocket.t port
        method listen =
          let s = socket PF_INET SOCK_STREAM 0 in
          sock <- Some s;
          setsockopt s SO_REUSEADDR true;
          bind s (ADDR_INET (inet_addr_any, port));
          listen s 256
        (* method close =
          match sock with
          | None -> ()
          | Some s -> shutdown s SHUTDOWN_ALL;
            close s;
            sock <- None *)
        method close_fork =
          match sock with
          | None -> ()
          | Some s -> close s;
            sock <- None
        method accept_fork =
          match sock with
          | None -> raise (Transport.E (Transport.NOT_OPEN, __MODULE__ ^
            ": Not listening but tried to accept"))
          | Some s -> let fd, _ = accept s in
            (new TChannelTransport.t
              (in_channel_of_descr fd, out_channel_of_descr fd),
              in_channel_of_descr fd, out_channel_of_descr fd)
      end
  end

module TReusableSocket =
  struct
    (** We need this subclass to call [close] without calling [shutdown]. *)
    class t host port =
      let open Unix in
      object
        inherit TSocket.t host port
        method close =
          match chans with
          | None -> ()
          | Some (ic, _) -> shutdown_connection ic;
            close_in ic;
            chans <- None
        method close_fork =
          match chans with
          | None -> ()
          | Some (ic, _) -> close_in ic;
            chans <- None
      end
  end

let start () =
  bracket
    ~acquire:begin fun () ->
      let strans = new TReusableServerSocket.t 9092 in
      strans
    end
    ~release:begin fun strans ->
      strans#close
    end
    begin fun strans ->
      Log.info (fun m -> m "Broker is listening.");
      strans#listen;
      while true do
        let trans, ic, oc = strans#accept_fork in
        match Unix.fork () with
        | 0 -> strans#close_fork;
          let proto = new TBinaryProtocol.t trans in
          let req = read_request proto in
          let value = Hashtbl.fold
            (fun i a y -> y +. a *. req#grab_point ** Int32.to_float i)
            req#grab_coeffs 0. in
          Unix.sleep 1;
          let res = new response in
          res#set_value value;
          res#write proto;
          proto#getTransport#flush;
          proto#getTransport#close;
          Log.debug (fun m -> m "Ended subprocess %d." (Unix.getpid ()));
          exit 0
        | pid -> (* trans#close_fork; *) close_in ic;
          Log.debug (fun m -> m "Started subprocess %d." pid)
      done
  end
