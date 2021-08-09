From DEZ.Has Require Export
  EquivalenceRelation GroupOperation.
From DEZ.Is Require Export
  Setoid.
From DEZ.ShouldHave Require Import
  AdditiveGroupNotations.

Class IsCommutative {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) : Prop := {
  eqv_is_setoid :> IsSetoid eqv;
  commutative : forall x y : A, x + y == y + x;
}.
