From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Multiplication OneSorted.One.
From Maniunfold.Is Require Export
  OneSorted.Commutative OneSorted.Monoid OneSorted.Distributive
  OneSorted.Absorbing.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

(** Noncommutative semiring. *)

Class IsSring (A : Type)
  (A_has_add : HasAdd A) (A_has_zero : HasZero A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A) : Prop := {
  A_add_is_comm :> IsComm A add;
  A_add_zero_is_mon :> IsMon A add zero;
  A_add_mul_is_distr :> IsDistr A add mul;
  A_zero_mul_is_absorb :> IsAbsorb A zero mul;
  A_mul_one_is_mon :> IsMon A mul one;
}.

Section Context.

Context {A : Type} `{is_sring : IsSring A}.

Ltac conversions := typeclasses
  convert bin_op into add and null_op into zero or
  convert bin_op into mul and null_op into one.

Goal 0 = 1 -> forall x y : A, x = y.
Proof with conversions.
  intros H x y.
  rewrite <- (l_unl (A_has_null_op := 1) x)...
  rewrite <- (l_unl (A_has_null_op := 1) y)...
  rewrite <- H.
  rewrite (l_absorb x).
  rewrite (l_absorb y).
  reflexivity. Defined.

End Context.
