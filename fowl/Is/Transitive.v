From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.

Fail Class IsTrans (A : Type) `(HasBinRel A) : Prop :=
  trans : forall x y z : A, x ~~ y -> y ~~ z -> x ~~ z.

Notation IsTrans bin_rel := (Transitive bin_rel).
Notation trans := (transitivity : IsTrans bin_rel).
