(* maybe *)
From DEZ Require Export
  Init.

(** Binary relation. *)

Class HasTwoBinRel (A B : Type) : Type := two_bin_rel : A -> B -> Prop.

#[export] Typeclasses Transparent HasTwoBinRel.
