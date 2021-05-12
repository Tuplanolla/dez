From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.

Fail Class IsSym (A : Type) `(HasBinRel A) : Prop :=
  sym (x y : A) (a : x ~~ y) : y ~~ x.

Notation IsSym bin_rel := (Symmetric bin_rel).
Notation sym := (symmetry (R := bin_rel)).
