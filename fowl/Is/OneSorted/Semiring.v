From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Multiplication OneSorted.One.
From Maniunfold.Is Require Export
  OneSorted.Commutative OneSorted.Monoid OneSorted.Distributive
  OneSorted.Absorbing.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

(** Noncommutative semiring. *)

Class IsSring (A : Type)
  `(HasAdd A) `(HasZero A)
  `(HasMul A) `(HasOne A) : Prop := {
  A_add_is_comm :> IsComm add;
  A_add_zero_is_mon :> IsMon add zero;
  A_add_mul_is_distr :> IsDistr add mul;
  A_zero_mul_is_absorb :> IsAbsorb zero mul;
  A_mul_one_is_mon :> IsMon mul one;
}.

Section Context.

Context (A : Type) `{IsSring A}.

Ltac conversions := typeclasses
  convert bin_op into add and null_op into zero or
  convert bin_op into mul and null_op into one.

Goal 0 = 1 -> forall x y : A, x = y.
Proof with conversions.
  intros Hyp x y.
  rewrite <- (l_unl (H0 := 1) x)...
  rewrite <- (l_unl (H0 := 1) y)...
  rewrite <- Hyp.
  rewrite (l_absorb x).
  rewrite (l_absorb y).
  reflexivity. Defined.

End Context.
