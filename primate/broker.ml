open Polynomial_types
open Thrift
open Util

module Log = (val Logs.src_log (Logs.Src.create "maniunfold.primate"))

(** We need to extend [Transport]
    with capabilities to [close] a socket without [shutdown].
    We also add [SO_REUSEADDR] to the socket options.
    As you can see, object-oriented programming was a mistake. *)

module ForkableTransport =
  struct
    class virtual t =
      object
        inherit Transport.t
        method virtual close_fork : unit
      end

    class virtual server_t =
      object
        inherit Transport.server_t
        method virtual accept_fork : t
        method virtual close_fork : unit
      end
  end

module TForkableChannelTransport =
  struct
    class t (ic, oc) =
      object (self)
        inherit ForkableTransport.t
        inherit TChannelTransport.t (ic, oc)
        method close_fork = self#close
      end
    end

module TForkableSocket =
  struct
    class t host port =
      object
        inherit ForkableTransport.t
        inherit TSocket.t host port
        method close_fork =
          match chans with
          | None -> ()
          | Some (ic, _) ->
              close_in ic;
              chans <- None
      end
    end

module TForkableServerSocket =
  struct
    class t port =
      let open Unix in
      object
        inherit ForkableTransport.server_t
        inherit TServerSocket.t port
        method listen =
          let s = socket PF_INET SOCK_STREAM 0 in
          sock <- Some s;
          setsockopt s SO_REUSEADDR true;
          bind s (ADDR_INET (inet_addr_any, port));
          listen s 256
        method accept_fork =
          match sock with
          | None -> raise (Transport.E (Transport.NOT_OPEN, "TForkableSocket"))
          | Some s ->
              let fd, _ = accept s in
              new TForkableChannelTransport.t
              (in_channel_of_descr fd, out_channel_of_descr fd)
        method close_fork =
          match sock with
          | None -> ()
          | Some s ->
              close s;
              sock <- None
      end
    end

(** We cannot use [TThreadedServer] here,
    because threads get blocked on system calls. *)

let start () =
  bracket
    ~acquire:begin fun () ->
      let strans = new TForkableServerSocket.t 9092 in
      strans
    end
    ~release:begin fun strans ->
      strans#close
    end
    begin fun strans ->
      Log.info (fun m -> m "Process is listening.");
      strans#listen;
      while true do
        let trans = strans#accept_fork in
        match Unix.fork () with
        | 0 -> strans#close_fork;
          let proto = new TBinaryProtocol.t (trans :> Transport.t) in
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
        | pid -> trans#close_fork;
          Log.debug (fun m -> m "Started subprocess %d." pid)
      done
  end
