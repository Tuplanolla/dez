(** * Semiring (bad) *)

From Maniunfold Require Export
  TypeclassTactics.
From Maniunfold.Has Require Export
  Addition Zero Multiplication One.
From Maniunfold.Is Require Export
  Commutative Monoid Distributive
  OneSortedAbsorbing.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations.

Class IsSemiring (A : Type)
  (Hk : HasAdd A) (Hx : HasZero A)
  (Hm : HasMul A) (Hy : HasOne A) : Prop := {
  add_zero_is_mon :> IsMon zero add;
  mul_one_is_mon :> IsMon one mul;
  add_is_comm :> IsComm add;
  add_mul_is_distr :> IsDistr mul add;
  zero_mul_is_absorb :> IsAbsorb zero mul;
}.

Section Context.

Context (A : Type) `(IsSemiring A).

Ltac conversions := typeclasses
  convert bin_op into add and null_op into zero or
  convert bin_op into mul and null_op into one.

Goal 0 = 1 -> forall x y : A, x = y.
Proof with conversions.
  intros e x y.
  pose proof @l_unl _ mul one _ as l...
  rewrite <- (l x).
  rewrite <- (l y).
  rewrite <- e.
  rewrite (l_absorb x).
  rewrite (l_absorb y).
  reflexivity. Qed.

End Context.
