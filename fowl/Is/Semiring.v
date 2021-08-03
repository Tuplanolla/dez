(** * Semiring *)

From Maniunfold Require Export
  TypeclassTactics.
From Maniunfold.Has Require Export
  Addition Zero Multiplication One.
From Maniunfold.Is Require Export
  Monoid Commutative Distributive Absorbing Degenerate.
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

#[local] Instance is_degen : IsDegen 0 1.
Proof.
  intros a x y.
  assert (f : forall z : A, z = 0).
  { intros z.
    pose proof f_equal (_*_ z) a as b.
    rewrite (unl_bin_op_r z) in b.
    rewrite (absorb_elem_r z) in b.
    rewrite b.
    reflexivity. }
  rewrite (f x), (f y).
  reflexivity. Qed.

End Context.
