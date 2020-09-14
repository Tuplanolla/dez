open Thrift

class t port =
  let open Unix in
  let open ThreadUnix in
  object
    inherit TServerSocket.t port
    method listen =
      let s = socket PF_INET SOCK_STREAM 0 in
      sock <- Some s;
      setsockopt s SO_REUSEADDR true;
      bind s (ADDR_INET (inet_addr_any, port));
      listen s 256
    method close =
      match sock with
      | None -> ()
      | Some s ->
          shutdown s SHUTDOWN_ALL;
          close s;
          sock <- None
    method acceptImpl =
      match sock with
      | None ->
          raise begin
            Transport.E begin
              Transport.NOT_OPEN,
              "TThreadedServerSocket: Not listening but tried to accept"
            end
          end
      | Some s ->
          let fd, _ = accept s in
          new TChannelTransport.t begin
            in_channel_of_descr fd,
            out_channel_of_descr fd
          end
  end
