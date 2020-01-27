open Big_int
open Extraction

val big_int_of_pos : positive -> big_int
(** Convert a positive integer tree into a big integer. *)

val big_int_of_z : z -> big_int
(** Convert an integer tree into a big integer. *)

val pos_of_big_int : big_int -> positive
(** Convert a big integer into a positive integer tree.
    Raise [Invalid_argument] if the big integer is negative. *)

val z_of_big_int : big_int -> z
(** Convert a big integer into an integer tree. *)

val z_of_int : int -> z
(** Convert a small integer into an integer tree. *)

val string_of_z : z -> string
(** Return the string representation of the given integer tree in base 10. *)
