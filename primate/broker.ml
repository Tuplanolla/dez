let () =
  (** Start `fur` process, start `scales` process,
      listen to `scales`, get message from `scales`, either:
      forward message to `fur`, get message from `fur`,
      forward message to `scales`, repeat; or:
      stop processes, exit. *)
  print_endline "magic"
