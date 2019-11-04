From Maniunfold.Has Require Export
  HigherEquivalenceRelation.
From Maniunfold.Is Require Export
  Setoid.

Class IsSetoidoid {A : Type}
  {has_arrow : HasArrow A} (has_hieqv : HasHiEqv arrow) : Prop := {
  hieqv_setoid : forall x y : A, IsSetoid (hieqv (x := x) (y := y));
}.
