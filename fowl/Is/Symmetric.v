From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.

Fail Class IsSym (A : Type) `(HasBinRel A) : Prop :=
  sym : forall x y : A, x ~~ y -> y ~~ x.

Notation IsSym bin_rel := (Symmetric bin_rel).
Notation sym := (symmetry : IsSym bin_rel).
