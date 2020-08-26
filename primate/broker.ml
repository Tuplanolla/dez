open Component_types
open Polynomial_types
open Thrift
open Util

module Log = (val Logs.src_log (Logs.Src.create "maniunfold.primate"))

(** We need to extend [Transport]
    with capabilities to [close] a socket without [shutdown].
    We also add [SO_REUSEADDR] to the socket options.
    As you can see, object-oriented programming was a mistake. *)

module ParallelTransport =
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

module TParallelChannelTransport =
  struct
    class t (ic, oc) =
      object (self)
        inherit ParallelTransport.t
        inherit TChannelTransport.t (ic, oc)
        method close_fork = self#close
      end
  end

module TParallelSocket =
  struct
    class t host port =
      object
        inherit ParallelTransport.t
        inherit TSocket.t host port
        method close_fork =
          match chans with
          | None -> ()
          | Some (ic, _) ->
              close_in ic;
              chans <- None
      end
  end

module TParallelServerSocket =
  struct
    class t port =
      let open Unix in
      object
        inherit ParallelTransport.server_t
        inherit TServerSocket.t port
        method listen =
          let s = socket PF_INET SOCK_STREAM 0 in
          sock <- Some s;
          setsockopt s SO_REUSEADDR true;
          bind s (ADDR_INET (inet_addr_any, port));
          listen s 256
        method accept_fork =
          match sock with
          | None -> raise
              (Transport.E (Transport.NOT_OPEN, "TParallelServerSocket"))
          | Some s ->
              let fd, _ = accept s in
              new TParallelChannelTransport.t
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
      (** This is the only unregistered port
          that is both prime and has a trivial binary representation. *)
      new TParallelServerSocket.t 8191
    end
    ~release:begin fun strans ->
      strans#close
    end
    begin fun strans ->
      Log.info (fun m -> m "Process is listening.");
      strans#listen;
      (** TODO Now pool connections here and start brokering! *)
      let tbl = Hashtbl.create 0 in
      while true do
        let trans = strans#accept_fork in
        match Unix.fork () with
        | 0 ->
            finally
              ~release:begin fun () ->
                exit 0
              end
              begin fun () ->
                strans#close_fork;
                (** TODO Read an identification message and,
                    based on it, choose the protocol.
                    The following assumes "one-shot gui". *)
                let proto = new TBinaryProtocol.t (trans :> Transport.t) in
                let id = read_identity proto in
                match id#grab_name with
                | "fur" ->
                    raise (Invalid_argument "Not supported yet")
                | "scales" ->
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
                    Log.debug (fun m -> m "Ended subprocess %d." (Unix.getpid ()))
                | name ->
                    raise (Invalid_argument name)
              end
        | pid ->
            trans#close_fork;
            Log.debug (fun m -> m "Started subprocess %d." pid)
      done
    end
