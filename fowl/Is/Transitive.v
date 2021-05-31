From Maniunfold.Has Require Export
  OneSortedBinaryRelation.

(* Class IsTrans (A : Type) `(HasBinRel A) : Prop :=
  trans (x y z : A) (a : x ~~ y) (b : y ~~ z) : x ~~ z. *)

Notation IsTrans := Transitive.
Notation trans := (transitivity (R := bin_rel)).
