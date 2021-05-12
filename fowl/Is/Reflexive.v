From Maniunfold.Has Require Export
  OneSortedBinaryRelation.

Fail Class IsRefl (A : Type) `(HasBinRel A) : Prop :=
  refl (x : A) : x ~~ x.

Notation IsRefl bin_rel := (Reflexive bin_rel).
Notation refl := (reflexivity (R := bin_rel)).
