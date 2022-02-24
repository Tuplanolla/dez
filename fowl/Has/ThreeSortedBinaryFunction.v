(* maybe *)
From DEZ Require Export
  Init.

(** Binary function. *)

Class HasBinFn (A B C : Type) : Type := bin_fn : A -> B -> C.

#[export] Typeclasses Transparent HasBinFn.
