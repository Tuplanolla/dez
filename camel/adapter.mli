open Big_int
open BinNums

(** Convert a positive integer tree into a big integer. *)
val big_int_of_pos : positive -> big_int

(** Convert an integer tree into a big integer. *)
val big_int_of_z : coq_Z -> big_int

(** Convert a big integer into a positive integer tree.
    Raise [Invalid_argument] if the big integer is negative. *)
val pos_of_big_int : big_int -> positive

(** Convert a big integer into an integer tree. *)
val z_of_big_int : big_int -> coq_Z

(** Convert a small integer into an integer tree. *)
val z_of_int : int -> coq_Z

(** Return the string representation of the given integer tree in base 10. *)
val string_of_z : coq_Z -> string
