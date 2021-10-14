(** * Ring Structure *)

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
  Semiring Unital.
From DEZ.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations ArithmeticNotations.

(** ** Ring *)

Class IsRing (A : Type) (R : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A)
  (y : A) (m : A -> A -> A) : Prop := {
  add_is_grp :> IsGrp R x f k;
  add_is_comm :> IsComm R k;
  mul_is_mon :> IsMon R y m;
  is_distr_l_r :> IsDistrLR R m k;
}.

(** TODO Clean up. *)

Section Context.

Context (A : Type) (R : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A)
  (y : A) (m : A -> A -> A) `(!IsRing R x f k y m).

#[local] Instance has_eq_rel : HasEqRel A := R.
#[local] Instance has_zero : HasZero A := x.
#[local] Instance has_neg : HasNeg A := f.
#[local] Instance has_add : HasAdd A := k.
#[local] Instance has_one : HasOne A := y.
#[local] Instance has_mul : HasMul A := m.

Ltac notate :=
  change R with _==_ in *;
  change x with 0 in *;
  change f with -_ in *;
  change k with _+_ in *;
  change y with 1 in *;
  change m with _*_ in *.

Import Zero.Subclass Negation.Subclass Addition.Subclass
  One.Subclass Multiplication.Subclass.

Ltac conversions := typeclasses
  convert null_op into zero and un_op into neg and bin_op into add or
  convert null_op into one and bin_op into mul.

#[local] Instance is_absorb_elem_l : IsAbsorbElemL R x m.
Proof with conversions.
  notate.
  intros z.
  apply (cancel_r (0 * z) 0 (1 * z))...
  setoid_rewrite <- (distr_r 0 1 z).
  setoid_rewrite (unl_l 1).
  setoid_rewrite (unl_l z).
  reflexivity. Qed.

#[local] Instance is_absorb_elem_r : IsAbsorbElemR R x m.
Proof with conversions.
  notate.
  intros z.
  apply (cancel_r (z * 0) 0 (z * 1))...
  setoid_rewrite <- (distr_l z 0 1).
  setoid_rewrite (unl_l 1).
  setoid_rewrite (unl_r z).
  reflexivity. Qed.

#[local] Instance is_absorb_elem_l_r : IsAbsorbElemLR R x m.
Proof. split; typeclasses eauto. Qed.

#[local] Instance is_semiring : IsSemiring R x k y m.
Proof. split; typeclasses eauto. Qed.

#[local] Instance is_comm_l : IsCommL R f m.
Proof with conversions.
  notate.
  intros z w.
  apply (cancel_l (z * (- w)) (- (z * w)) (z * w))...
  setoid_rewrite <- (distr_l z w (- w)).
  setoid_rewrite (inv_r w).
  setoid_rewrite (absorb_elem_r z).
  setoid_rewrite (inv_r (z * w)).
  reflexivity. Qed.

#[local] Instance is_comm_r : IsCommR R f m.
Proof with conversions.
  notate.
  intros z w.
  apply (cancel_l ((- z) * w) (- (z * w)) (z * w))...
  setoid_rewrite <- (distr_r z (- z) w).
  setoid_rewrite (inv_r z).
  setoid_rewrite (absorb_elem_l w).
  setoid_rewrite (inv_r (z * w)).
  reflexivity. Qed.

#[local] Instance is_comm_l_r : IsCommLR R f m.
Proof. split; typeclasses eauto. Qed.

Lemma comm_l_r (z w : A) : (- z) * w == z * (- w).
Proof with conversions.
  notate.
  setoid_rewrite (comm_l z w).
  setoid_rewrite (comm_r z w).
  reflexivity. Qed.

Lemma invol_l_r (z w : A) : (- z) * (- w) == z * w.
Proof with conversions.
  notate.
  setoid_rewrite (comm_l (- z) w).
  setoid_rewrite (comm_r z w).
  setoid_rewrite (invol (z * w)).
  reflexivity. Qed.

Lemma neg_mul_one_l_sgn_absorb (z : A) : (- 1) * z == - z.
Proof with conversions.
  notate.
  setoid_rewrite (comm_r 1 z).
  setoid_rewrite (unl_l z).
  reflexivity. Qed.

Lemma neg_mul_one_r_sgn_absorb (z : A) : z * (- 1) == - z.
Proof with conversions.
  setoid_rewrite (comm_l z 1).
  setoid_rewrite (unl_r z).
  reflexivity. Qed.

Instance integral_domain_thing
  (a : forall z w : A, z * w == 0 -> z == 0 \/ w == 0) :
  IsNonzeroCancelL 0 _*_.
Proof with conversions.
  intros z w v g e.
  replace (@eq A) with _==_ in * by admit.
  typeclasses convert null_op into zero and bin_op into mul.
  assert (e' : v * z + - (v * w) == 0).
  { setoid_rewrite e.
    setoid_rewrite (inv_r (v * w)).
    reflexivity. }
  setoid_rewrite <- comm_l in e'.
  setoid_rewrite <- distr_l in e'.
  apply a in e'.
  destruct e' as [e' | e'].
  - congruence.
  - apply (cancel_r z w (- w))...
    setoid_rewrite e'.
    setoid_rewrite (inv_r w).
    reflexivity. Admitted.

End Context.
