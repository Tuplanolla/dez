(** * Semiring *)

From DEZ.Has Require Export
  Addition Zero Multiplication One.
From DEZ.Is Require Export
  Monoid Commutative Distributive Absorbing Truncated.
From DEZ.ShouldHave Require Import
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

#[local] Instance is_contr (a : 0 = 1) : IsContr A.
Proof.
  hnf.
  exists 0.
  intros x.
  pose proof f_equal (_*_ x) a as b.
  setoid_rewrite (unl_bin_op_r x) in b.
  rewrite (absorb_elem_r x) in b.
  rewrite b.
  reflexivity. Qed.

End Context.

#[export] Hint Resolve is_contr : typeclass_instances.
