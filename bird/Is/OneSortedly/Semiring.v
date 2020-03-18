From Maniunfold.Has Require Export
  EquivalenceRelation Addition Multiplication.
From Maniunfold.Is Require Export
  Commutative Monoid Distributive Absorbing.
From Maniunfold.ShouldHave Require Import
  ArithmeticNotations.

(** This is a unital semiring. *)

Class IsSring {A : Type}
  (has_add : HasAdd A) (has_zero : HasZero A)
  (has_mul : HasMul A) (has_one : HasOne A) : Prop := {
  add_is_comm :> IsComm add;
  add_zero_is_mon :> IsMon add zero;
  add_mul_is_distr :> IsDistr add mul;
  zero_mul_is_absorb :> IsAbsorb zero mul;
  mul_one_is_mon :> IsMon mul one;
}.

Section Context.

Context {A : Type} `{is_sring : IsSring A}.

Ltac specializations := typeclasses specialize
  bin_op into add and null_op into zero or
  bin_op into mul and null_op into one.

Goal 0 = 1 -> forall x y : A, x = y.
Proof with specializations.
  intros H x y.
  rewrite <- (l_unl (A_has_null_op := 1) x)...
  rewrite <- (l_unl (A_has_null_op := 1) y)...
  rewrite <- H.
  rewrite (l_absorb x).
  rewrite (l_absorb y).
  reflexivity. Qed.

End Context.
