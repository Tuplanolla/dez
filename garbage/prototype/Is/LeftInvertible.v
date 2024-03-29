From DEZ.Has Require Export
  EquivalenceRelation GroupOperation GroupIdentity GroupInverse.
From DEZ.Is Require Export
  Setoid.
From DEZ.ShouldHave Require Import
  AdditiveGroupNotations.

Class IsLeftInvertible {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) (has_idn : HasIdn A) (has_inv : HasInv A) : Prop := {
  eqv_is_setoid :> IsSetoid eqv;
  left_invertible : forall x : A, (- x) + x == 0;
}.
