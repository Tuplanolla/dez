(** * Ring Structure *)

From Coq Require Import
  Logic.Eqdep_dec.
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

Class IsRing (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A)
  (y : A) (m : A -> A -> A) : Prop := {
  add_is_grp :> IsGrp X x f k;
  add_is_comm :> IsComm X k;
  mul_is_mon :> IsMon X y m;
  is_distr_l_r :> IsDistrLR X m k;
}.

(** TODO Clean up. *)

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A)
  (y : A) (m : A -> A -> A)
  `(!IsRing X x f k y m).

(** Declare the underlying equivalence relation as an equivalence relation and
    the underlying operations as operations. *)

#[local] Instance has_eq_rel : HasEqRel A := X.
#[local] Instance has_zero : HasZero A := x.
#[local] Instance has_neg : HasNeg A := f.
#[local] Instance has_add : HasAdd A := k.
#[local] Instance has_one : HasOne A := y.
#[local] Instance has_mul : HasMul A := m.

Ltac note := progress (
  try change X with eq_rel in *;
  try change x with zero in *;
  try change f with neg in *;
  try change k with add in *;
  try change y with one in *;
  try change m with mul in *).

(** Specialize binary relations into the underlying equivalence relation and
    either specialize operations into the underlying additive operations or
    specialize operations into the underlying multiplicative operations. *)

Import Zero.Subclass Negation.Subclass Addition.Subclass
  One.Subclass Multiplication.Subclass.

Ltac subclass := progress (
  try change bin_rel with eq_rel in *;
  try change null_op with zero in *;
  try change un_op with neg in *;
  try change bin_op with add in *;
  try change null_op with one in *;
  try change bin_op with mul in *).

#[local] Instance is_absorb_elem_l : IsAbsorbElemL X x m.
Proof.
  note.
  intros z.
  apply (cancel_r (0 * z) 0 (1 * z)); subclass.
  setoid_rewrite <- (distr_r 0 1 z).
  setoid_rewrite (unl_l 1).
  setoid_rewrite (unl_l z).
  reflexivity. Qed.

#[local] Instance is_absorb_elem_r : IsAbsorbElemR X x m.
Proof with subclass.
  note.
  intros z.
  apply (cancel_r (z * 0) 0 (z * 1))...
  setoid_rewrite <- (distr_l z 0 1).
  setoid_rewrite (unl_l 1).
  setoid_rewrite (unl_r z).
  reflexivity. Qed.

#[local] Instance is_absorb_elem_l_r : IsAbsorbElemLR X x m.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance is_semiring : IsSemiring X x k y m.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance is_comm_l : IsCommL X f m.
Proof with subclass.
  note.
  intros z w.
  apply (cancel_l (z * (- w)) (- (z * w)) (z * w))...
  setoid_rewrite <- (distr_l z w (- w)).
  setoid_rewrite (inv_r w).
  setoid_rewrite (absorb_elem_r z).
  setoid_rewrite (inv_r (z * w)).
  reflexivity. Qed.

#[local] Instance is_comm_r : IsCommR X f m.
Proof with subclass.
  note.
  intros z w.
  apply (cancel_l ((- z) * w) (- (z * w)) (z * w))...
  setoid_rewrite <- (distr_r z (- z) w).
  setoid_rewrite (inv_r z).
  setoid_rewrite (absorb_elem_l w).
  setoid_rewrite (inv_r (z * w)).
  reflexivity. Qed.

#[local] Instance is_comm_l_r : IsCommLR X f m.
Proof. esplit; typeclasses eauto. Qed.

Lemma comm_l_r (z w : A) : (- z) * w == z * (- w).
Proof with subclass.
  note.
  setoid_rewrite (comm_l z w).
  setoid_rewrite (comm_r z w).
  reflexivity. Qed.

Lemma invol_l_r (z w : A) : (- z) * (- w) == z * w.
Proof with subclass.
  note.
  setoid_rewrite (comm_l (- z) w).
  setoid_rewrite (comm_r z w).
  setoid_rewrite (invol (z * w)).
  reflexivity. Qed.

Lemma neg_mul_one_l_sgn_absorb (z : A) : (- 1) * z == - z.
Proof with subclass.
  note.
  setoid_rewrite (comm_r 1 z).
  setoid_rewrite (unl_l z).
  reflexivity. Qed.

Lemma neg_mul_one_r_sgn_absorb (z : A) : z * (- 1) == - z.
Proof with subclass.
  setoid_rewrite (comm_l z 1).
  setoid_rewrite (unl_r z).
  reflexivity. Qed.

Instance integral_domain_thing
  (a : forall z w : A, z * w == 0 -> z == 0 \/ w == 0) :
  IsNonzeroCancelL _==_ 0 _*_.
Proof with subclass.
  intros z w v g e.
  subclass.
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
    reflexivity. Qed.

End Context.
