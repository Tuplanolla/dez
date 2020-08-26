(** Manage the scope of a resource.

    Note that [~release] is not called
    if the process is terminated by an unhandled signal. *)
val finally : (unit -> 'b) -> release:(unit -> unit) -> 'b

(** Manage the scope of a resource.

    Note that [~release] is not called
    if the process is terminated by an unhandled signal. *)
val bracket : acquire:(unit -> 'a) -> ('a -> 'b) -> release:('a -> unit) -> 'b

(** Is the given string a prefix of the other given string? *)
val string_is_prefix : string -> string -> bool
