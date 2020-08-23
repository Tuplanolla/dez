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

(** Defunctionalized version of [Sys.signal_behavior]. *)
type signal_behavior =
  | Signal_default
  | Signal_ignore
  | Signal_raise
  | Signal_skip

(** Defunctionalized version of [Sys.set_signal]. *)
val set_signal : int -> signal_behavior -> unit
