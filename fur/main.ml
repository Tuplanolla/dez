(** TODO Write this like the broker's main. *)

(** Configure and start the server. *)
let main () =
  Server_proxy.start ()

let () =
  main ()
