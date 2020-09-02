(** The port the broker listens on.

    This is the only port number that
    - is in the user ports range from 1024 to 49151,
    - has not already been assigned to another use by IANA,
    - has a nice binary representation and
    - is prime. *)
val broker_port : int

(** Start the broker. *)
val start : unit -> unit
