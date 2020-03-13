From Maniunfold.Has Require Export
  EquivalenceRelation Addition Multiplication.
From Maniunfold.Is Require Export
  Commutative Monoid Distributive Absorbing.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations.

Class IsSring {A : Type}
  (has_add : HasAdd A) (has_zero : HasZero A)
  (has_mul : HasMul A) (has_one : HasOne A) : Prop := {
  add_is_comm :> IsComm add;
  add_zero_is_mon :> IsMon add zero;
  add_mul_is_distr :> IsDistr add mul;
  zero_mul_is_absorb :> IsAbsorb zero mul;
  mul_one_is_mon :> IsMon mul one;
}.

Ltac change_add_mon :=
  change bin_op with add in *;
  change un with zero in *.

Ltac change_mul_mon :=
  change bin_op with mul in *;
  change un with one in *.

Section Context.

Context {A : Type} `{is_sring : IsSring A}.

Goal 0 = 1 -> forall x y : A, x = y.
Proof with change_add_mon || change_mul_mon.
  intros H x y.
  rewrite <- (l_unl x)...
  rewrite <- (l_unl y)...
  rewrite <- H.
  rewrite (l_absorb x)...
  rewrite (l_absorb y)...
  reflexivity. Qed.

End Context.
