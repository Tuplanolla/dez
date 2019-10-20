From Maniunfold.Has Require Export
  EquivalenceRelation Distance.
From Maniunfold.Is Require Export
  Setoid.

Class IsHeterocommutative {S A : Type} {has_eqv : HasEqv S}
  (has_dist : HasDist S A) : Prop := {
  eqv_is_setoid :> IsSetoid eqv;
  heterocommutative : forall x y : A, dist x y == dist y x;
}.
