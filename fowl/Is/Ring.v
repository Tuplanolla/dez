(** * Ring *)

From Coq Require Import
  Logic.Eqdep_dec.
From DEZ Require Export
  TypeclassTactics.
From DEZ.Has Require Export
  Zero Negation Addition One Multiplication.
From DEZ.Is Require Export
  Group Commutative Monoid Distributive
  Cancellative Absorbing OneSortedSignedAbsorbing OneSortedBinaryCommutative
  OneSortedBinaryCrossing OneSortedBinarySplitCancellative
  Semiring OneSortedGradedRing
  Unital.
From DEZ.ShouldHave Require Import
  AdditiveNotations ArithmeticNotations.
From DEZ.ShouldHave Require
  OneSortedGradedAdditiveNotations OneSortedGradedArithmeticNotations.

Class IsRing (A : Type)
  (Hx : HasZero A) (Hf : HasNeg A) (Hk : HasAdd A)
  (Hy : HasOne A) (Hm : HasMul A) : Prop := {
  add_is_grp :> IsGrp 0 -_ _+_;
  add_is_comm :> IsCommBinOp _+_;
  mul_is_mon :> IsMon 1 _*_;
  is_distr_l_r :> IsDistrLR _*_ _+_;
}.

(** TODO Clean up. *)

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
  setoid_rewrite (unl_bin_op_l 1).
  setoid_rewrite (unl_bin_op_l x).
  reflexivity. Qed.

#[local] Instance is_absorb_elem_r : IsAbsorbElemR 0 _*_.
Proof with conversions.
  intros x.
  apply (cancel_r (x * 0) 0 (x * 1))...
  rewrite <- (distr_l x 0 1).
  setoid_rewrite (unl_bin_op_l 1).
  setoid_rewrite (unl_bin_op_r x).
  reflexivity. Qed.

#[local] Instance is_absorb_elem_l_r : IsAbsorbElemLR 0 _*_.
Proof. split; typeclasses eauto. Qed.

#[local] Instance is_semiring : IsSemiring 0 _+_ 1 _*_.
Proof. split; typeclasses eauto. Qed.

#[local] Instance is_comm_l : IsCommL -_ _*_.
Proof with conversions.
  intros x y.
  typeclasses convert un_op into neg and bin_op into mul.
  apply (cancel_l ((- x) * y) (- (x * y)) (x * y))...
  rewrite <- (distr_r x (- x) y).
  setoid_rewrite (inv_r x)...
  rewrite (absorb_elem_l y).
  setoid_rewrite (inv_r (x * y))...
  reflexivity. Qed.

#[local] Instance is_comm_r : IsCommR -_ _*_.
Proof with conversions.
  intros x y.
  typeclasses convert un_op into neg and bin_op into mul.
  apply (cancel_l (x * (- y)) (- (x * y)) (x * y))...
  rewrite <- (distr_l x y (- y)).
  setoid_rewrite (inv_r y)...
  rewrite (absorb_elem_r x).
  setoid_rewrite (inv_r (x * y))...
  reflexivity. Qed.

#[local] Instance is_comm_l_r : IsCommLR -_ _*_.
Proof. split; typeclasses eauto. Qed.

Lemma comm_l_r (x y : A) : (- x) * y = x * (- y).
Proof with conversions.
  setoid_rewrite (comm_l x y)...
  setoid_rewrite (comm_r x y)...
  reflexivity. Qed.

Lemma invol_l_r (x y : A) : (- x) * (- y) = x * y.
Proof with conversions.
  setoid_rewrite (comm_l x (- y))...
  setoid_rewrite (comm_r x y)...
  rewrite (invol (x * y)).
  reflexivity. Qed.

Lemma neg_mul_one_l_sgn_absorb (x : A) : (- 1) * x = - x.
Proof with conversions.
  setoid_rewrite (comm_l 1 x).
  rewrite (unl_bin_op_l x).
  reflexivity. Qed.

Lemma neg_mul_one_r_sgn_absorb (x : A) : x * (- 1) = - x.
Proof with conversions.
  setoid_rewrite (comm_r x 1).
  rewrite (unl_bin_op_r x).
  reflexivity. Qed.

Global Instance integral_domain_thing
  (a : forall x y : A, x * y = 0 -> x = 0 \/ y = 0) : IsNonzeroCancelL 0 _*_.
Proof with conversions.
  intros x y z f e.
  typeclasses convert null_op into zero and bin_op into mul.
  assert (e' : z * x + - (z * y) = 0).
  { rewrite e.
    setoid_rewrite (inv_r (z * y))...
    reflexivity. }
  setoid_rewrite <- comm_r in e'...
  typeclasses convert un_op into neg.
  rewrite <- distr_l in e'.
  apply a in e'.
  destruct e' as [e' | e'].
  - congruence.
  - apply (cancel_r x y (- y))...
    rewrite e'.
    setoid_rewrite (inv_r y)...
    reflexivity. Qed.

End Context.
