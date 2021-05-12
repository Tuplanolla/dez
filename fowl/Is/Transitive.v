From Maniunfold.Has Require Export
  OneSortedBinaryRelation.

Fail Class IsTrans (A : Type) `(HasBinRel A) : Prop :=
  trans (x y z : A) (a : x ~~ y) (b : y ~~ z) : x ~~ z.

Notation IsTrans bin_rel := (Transitive bin_rel).
Notation trans := (transitivity (R := bin_rel)).
