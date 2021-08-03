(** * Semiring *)

From Maniunfold Require Export
  TypeclassTactics.
From Maniunfold.Has Require Export
  Addition Zero Multiplication One.
From Maniunfold.Is Require Export
  Monoid Commutative Distributive Absorbing.
From Maniunfold.ShouldHave Require Import
  ArithmeticNotations.

Class IsSemiring (A : Type)
  (Hx : HasZero A) (Hk : HasAdd A) (Hy : HasOne A) (Hm : HasMul A) : Prop := {
  add_is_mon :> IsMon 0 _+_;
  add_is_comm :> IsCommBinOp _+_;
  mul_is_mon :> IsMon 1 _*_;
  is_distr_l_r :> IsDistrLR _*_ _+_;
  is_absorb_elem_l_r :> IsAbsorbElemLR 0 _*_;
}.

Section Context.

Context (A : Type) `(IsSemiring A).

Import Addition.Subclass Zero.Subclass Negation.Subclass
  Multiplication.Subclass One.Subclass.

Ltac conversions := typeclasses
  convert bin_op into add and null_op into zero or
  convert bin_op into mul and null_op into one.

Goal 0 = 1 -> forall x y : A, x = y.
Proof with conversions.
  intros e x y.
  rewrite <- (unl_bin_op_l x)...
  rewrite <- (unl_bin_op_l y)...
  rewrite <- e.
  rewrite (absorb_elem_l x).
  rewrite (absorb_elem_l y).
  reflexivity. Qed.

End Context.
