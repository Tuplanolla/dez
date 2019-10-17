From Maniunfold.Has Require Export
  EquivalenceRelation Endomorphism.
From Maniunfold.Is Require Export
  Setoid.

Class IsInvolutive {A : Type} {has_eqv : HasEqv A}
  (has_endo : HasEndo A) : Prop := {
  involutive_is_setoid :> IsSetoid eqv;
  involutive : forall x : A, endo (endo x) == x;
}.
