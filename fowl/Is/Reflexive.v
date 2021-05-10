From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.

Fail Class IsRefl (A : Type) `(HasBinRel A) : Prop :=
  refl (x : A) : x ~~ x.

Notation IsRefl bin_rel := (Reflexive bin_rel).
Notation refl := (reflexivity : IsRefl bin_rel).
