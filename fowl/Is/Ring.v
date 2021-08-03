(** * Ring *)

From Coq Require Import
  Logic.Eqdep_dec.
From Maniunfold Require Export
  TypeclassTactics.
From Maniunfold.Has Require Export
  Zero Negation Addition One Multiplication.
From Maniunfold.Is Require Export
  Group Commutative Monoid Distributive
  Cancellative Absorbing OneSortedSignedAbsorbing OneSortedBinaryCommutative
  OneSortedBinaryCrossing OneSortedBinarySplitCancellative
  OneSortedDegenerate OneSortedSemiring OneSortedGradedRing
  Unital.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations ArithmeticNotations.
From Maniunfold.ShouldHave Require
  OneSortedGradedAdditiveNotations OneSortedGradedArithmeticNotations.

Class IsRing (A : Type)
  (Hx : HasZero A) (Hf : HasNeg A) (Hk : HasAdd A)
  (Hy : HasOne A) (Hm : HasMul A) : Prop := {
  is_grp :> IsGrp 0 -_ _+_;
  is_comm :> IsComm _+_;
  is_mon :> IsMon 1 _*_;
  is_distr_l_r :> IsDistrLR _*_ _+_;
}.

Section Context.

Context (A : Type) `(IsRing A).

Import Zero.Subclass Negation.Subclass Addition.Subclass
  One.Subclass Multiplication.Subclass.

Ltac conversions := typeclasses
  convert null_op into zero and un_op into neg and bin_op into add or
  convert null_op into one and bin_op into mul.

#[local] Instance is_absorb_elem_l : IsAbsorbElemL 0 _*_.
Proof with conversions.
  intros x.
  apply (cancel_r (0 * x) 0 (1 * x))...
  rewrite <- (distr_r 0 1 x).
  rewrite (unl_bin_op_l 1).
  rewrite (unl_bin_op_l (1 * x)).
  reflexivity. Qed.

#[local] Instance is_absorb_elem_r : IsAbsorbElemR 0 _*_.
Proof with conversions.
  intros x.
  apply (cancel_r (x * 0) 0 (x * 1))...
  rewrite <- (distr_l x 0 1).
  rewrite (unl_bin_op_l 1).
  rewrite (unl_bin_op_l (x * 1)).
  reflexivity. Qed.

#[local] Instance is_absorb_elem_l_r : IsAbsorbElemLR 0 _*_.
Proof. split; typeclasses eauto. Qed.

Theorem neg_mul_one_l_sgn_absorb (x : A) : (- 1) * x = - x.
Proof with conversions.
  apply (cancel_l ((- 1) * x) (- x) (1 * x))...
  rewrite <- (distr_r 1 (- 1) x).
  rewrite (inv_r 1)...
  rewrite (absorb_elem_l x).
  rewrite (unl_bin_op_l x).
  rewrite (inv_r x)...
  reflexivity. Qed.

Global Instance neg_mul_one_is_l_sgn_absorb : IsLSgnAbsorb neg mul one.
Proof. exact @neg_mul_one_l_sgn_absorb. Qed.

Theorem neg_mul_one_r_sgn_absorb (x : A) : x * (- 1) = - x.
Proof with conversions.
  apply (cancel_l (x * (- 1)) (- x) (x * 1))...
  rewrite <- (distr_l x 1 (- 1)).
  rewrite (inv_r 1)...
  rewrite (absorb_elem_r x).
  rewrite (unl_bin_op_r x).
  rewrite (inv_r x)...
  reflexivity. Qed.

Global Instance neg_mul_one_is_r_sgn_absorb : IsRSgnAbsorb neg mul one.
Proof. exact @neg_mul_one_r_sgn_absorb. Qed.

Global Instance neg_mul_one_is_sgn_absorb : IsSgnAbsorb neg mul one.
Proof. split; typeclasses eauto. Qed.

Theorem neg_mul_l_bin_comm (x y : A) : - (x * y) = x * (- y).
Proof with conversions.
  rewrite <- (r_sgn_absorb (x * y)).
  rewrite <- (assoc x y (- 1))...
  rewrite r_sgn_absorb.
  reflexivity. Qed.

Global Instance neg_mul_is_l_bin_comm : IsLBinComm neg mul.
Proof. exact @neg_mul_l_bin_comm. Qed.

Theorem neg_mul_r_bin_comm (x y : A) : - (x * y) = (- x) * y.
Proof with conversions.
  rewrite <- (l_sgn_absorb (x * y)).
  rewrite (assoc (- 1) x y)...
  rewrite l_sgn_absorb.
  reflexivity. Qed.

Global Instance neg_mul_is_r_bin_comm : IsRBinComm neg mul.
Proof. exact @neg_mul_r_bin_comm. Qed.

Global Instance neg_mul_is_bin_comm : IsBinComm neg mul.
Proof. split; typeclasses eauto. Qed.

Theorem neg_mul_bin_crs (x y : A) : (- x) * y = x * (- y).
Proof with conversions.
  rewrite <- (l_bin_comm x y).
  rewrite <- (r_bin_comm x y).
  reflexivity. Qed.

Global Instance neg_mul_is_bin_crs : IsBinCrs neg mul.
Proof. exact @neg_mul_bin_crs. Qed.

Theorem neg_mul_bin_spt_cancel (x y : A) : (- x) * (- y) = x * y.
Proof with conversions.
  rewrite <- (r_bin_comm x (- y)).
  rewrite <- (l_bin_comm x y).
  rewrite (invol (x * y)).
  reflexivity. Qed.

Global Instance neg_mul_is_bin_spt_cancel : IsBinSptCancel neg mul.
Proof. exact @neg_mul_bin_spt_cancel. Qed.

Global Instance add_zero_mul_one_is_semiring : IsSemiring add zero mul one.
Proof. split; typeclasses eauto. Qed.

Theorem one_zero_degen (x : A) (e : 1 = 0) : x = 0.
Proof with conversions.
  pose proof distr_l x 0 1 as e'.
  rewrite unl_bin_op_l in e'. rewrite unl_bin_op_r in e' at 1. rewrite e in e'.
  repeat rewrite absorb_elem_r in e'. rewrite unl_bin_op_r in e'. apply e'. Qed.

Global Instance one_zero_is_degen : IsDegen zero one.
Proof. exact @one_zero_degen. Qed.

(** TODO Clean up. *)

Global Instance integral_domain_thing
  (a : forall x y : A, x * y = 0 -> x = 0 \/ y = 0) : IsNonzeroCancelL 0 _*_.
Proof with conversions.
  intros x y z f e.
  typeclasses convert null_op into zero and bin_op into mul.
  assert (e' : z * x + - (z * y) = 0).
  { rewrite e.
    rewrite (inv_r (z * y))...
    reflexivity. }
  rewrite l_bin_comm in e'.
  rewrite <- distr_l in e'.
  apply a in e'.
  destruct e' as [e' | e'].
  - congruence.
  - apply (cancel_r x y (- y))...
    rewrite e'.
    rewrite (inv_r y)...
    reflexivity. Qed.

End Context.
