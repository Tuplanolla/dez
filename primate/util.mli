(** A specialization of [Logs] with this project as the source. *)
module Log : Logs.LOG

(** All the standard POSIX signals. *)
val posix_signals : int array

(** Find the name of the given signal. *)
val string_of_signal : int -> string

(** Find the signal with the given name. *)
val signal_of_string : string -> int

(** Exception raised on a signal. *)
exception Signal of int

(** Raise a [Signal] exception for the given signal. *)
val raise_signal : int -> 'a

(** Make the given signals raise the [Signal] exception. *)
val catch_signals : int array -> unit

(** Make the given signals not raise the [Signal] exception or
    terminate the process. *)
val ignore_signals : int array -> unit

(** Manage the scope of a resource.

    Note that [~release] is not called
    if the process is terminated by an unhandled signal. *)
val bracket : acquire:(unit -> 'a) -> ('a -> 'b) -> release:('a -> unit) -> 'b

(** Is the given string a prefix of the other given string? *)
val string_is_prefix : string -> string -> bool
