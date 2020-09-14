open Thrift

class t host port =
  let open Unix in
  let open ThreadUnix in
  object
    inherit TSocket.t host port
    method isOpen = chans != None
    method opn =
      try
        let addr = (gethostbyname host).h_addr_list.(0) in
        chans <- Some (open_connection (ADDR_INET (addr, port)))
      with
      | Unix_error (e, fn, _) ->
          raise begin
            Transport.E begin
              Transport.NOT_OPEN,
              "TThreadedSocket: Could not connect to " ^
              host ^ ":" ^ string_of_int port ^
              " because: " ^ fn ^ ": " ^ error_message e
            end
          end
      | _ ->
          raise begin
            Transport.E begin
              Transport.NOT_OPEN,
              "TThreadedSocket: Could not connect to " ^
              host ^ ":" ^ string_of_int port
            end
          end
    method close =
      match chans with
      | None -> ()
      | Some (inc, out) ->
          shutdown_connection inc;
          close_in inc;
          chans <- None
    method read buf off len =
      match chans with
      | None ->
          raise begin
            Transport.E begin
              Transport.NOT_OPEN,
              "TThreadedSocket: Socket not open"
            end
          end
      | Some (i, o) ->
          try
            really_input i buf off len;
            len
          with
          | Unix_error (e, fn, _) ->
              raise begin
                Transport.E begin
                  Transport.UNKNOWN,
                  "TThreadedSocket: Could not read " ^ string_of_int len ^
                  " bytes from " ^ host ^ ":" ^ string_of_int port ^
                  " because: " ^ fn ^ ": " ^ error_message e
                end
              end
          | _ ->
              raise begin
                Transport.E begin
                  Transport.UNKNOWN,
                  "TThreadedSocket: Could not read " ^ string_of_int len ^
                  " bytes from " ^ host ^ ":" ^ string_of_int port
                end
              end
    method write buf off len =
      match chans with
      | None ->
          raise begin
            Transport.E begin
              Transport.NOT_OPEN,
              "TThreadedSocket: Socket not open"
            end
          end
      | Some (i, o) -> output o buf off len
    method write_string buf off len =
      match chans with
      | None ->
          raise begin
            Transport.E begin
              Transport.NOT_OPEN,
              "TThreadedSocket: Socket not open"
            end
          end
      | Some (i, o) -> output_substring o buf off len
    method flush =
      match chans with
      | None ->
          raise begin
            Transport.E begin
              Transport.NOT_OPEN,
              "TThreadedSocket: Socket not open"
            end
          end
      | Some (i, o) -> flush o
  end
