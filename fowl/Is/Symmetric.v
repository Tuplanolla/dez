From Maniunfold.Has Require Export
  OneSortedBinaryRelation.

(* Class IsSym (A : Type) `(HasBinRel A) : Prop :=
  sym (x y : A) (a : x ~~ y) : y ~~ x. *)

Notation IsSym := Symmetric.
Notation sym := (symmetry (R := bin_rel)).
