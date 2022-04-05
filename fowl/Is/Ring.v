(** * Ring Structure *)

From DEZ.Has Require Export
  EquivalenceRelations ArithmeticOperations Repetitions.
From DEZ.Is Require Export
  Group Commutative Monoid Distributive
  Absorbing Semiring Preserving Proper.
From DEZ.Supports Require Import
  EquivalenceNotations ArithmeticNotations.

(** ** Noncommutative Nonunital Ring *)

Class IsRng (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) (m : A -> A -> A) : Prop := {
  rng_add_is_grp :> IsGrp X x f k;
  rng_add_is_comm_bin_op :> IsCommBinOp X k;
  rng_mul_is_semigrp :> IsSemigrp X m;
  rng_is_distr :> IsDistr X m k;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) (m : A -> A -> A)
  `{!IsRng X x f k m}.

#[local] Instance rng_has_equiv_rel : HasEquivRel A := X.
#[local] Instance rng_has_zero : HasZero A := x.
#[local] Instance rng_has_neg : HasNeg A := f.
#[local] Instance rng_has_add : HasAdd A := k.
#[local] Instance rng_has_mul : HasMul A := m.

Ltac note := progress (
  try change X with (equiv_rel (A := A)) in *;
  try change x with (zero (A := A)) in *;
  try change f with (neg (A := A)) in *;
  try change k with (add (A := A)) in *;
  try change m with (mul (A := A)) in *).

(** Zero left-absorbs multiplication. *)

#[local] Instance rng_is_absorb_elem_l : IsAbsorbElemL X x m.
Proof with note.
  intros z...
  apply (cancel_r (0 * z) 0 (0 * z)).
  rewrite <- (distr_r 0 0 z).
  rewrite (unl_elem_l 0).
  rewrite (unl_elem_l (0 * z)).
  reflexivity. Qed.

(** Zero right-absorbs multiplication. *)

#[local] Instance rng_is_absorb_elem_r : IsAbsorbElemR X x m.
Proof with note.
  intros z...
  apply (cancel_r (z * 0) 0 (z * 0)).
  rewrite <- (distr_l z 0 0).
  rewrite (unl_elem_r 0).
  rewrite (unl_elem_l (z * 0)).
  reflexivity. Qed.

(** Zero absorbs multiplication. *)

#[export] Instance rng_is_absorb_elem : IsAbsorbElem X x m.
Proof. esplit; typeclasses eauto. Qed.

(** Removing negation from a nonunital ring yields a nonunital semiring. *)

#[export] Instance rng_is_semirng : IsSemirng X x k m.
Proof. esplit; typeclasses eauto. Qed.

(** Multiplication left-commutes with negation. *)

#[local] Instance rng_is_comm_l : IsCommL X m f.
Proof with note.
  intros z w...
  apply (cancel_l (z * w) ((- z) * w) (- (z * w))).
  rewrite <- (distr_r z (- z) w).
  rewrite (inv_r z).
  rewrite (absorb_elem_l w).
  rewrite (inv_r (z * w)).
  reflexivity. Qed.

(** Multiplication right-commutes with negation. *)

#[local] Instance rng_is_comm_r : IsCommR X m f.
Proof with note.
  intros z w...
  apply (cancel_l (z * w) (z * (- w)) (- (z * w))).
  rewrite <- (distr_l z w (- w)).
  rewrite (inv_r w).
  rewrite (absorb_elem_r z).
  rewrite (inv_r (z * w)).
  reflexivity. Qed.

(** Multiplication commutes with negation. *)

#[export] Instance rng_is_comm : IsComm X m f.
Proof. esplit; typeclasses eauto. Qed.

Lemma rng_comm_invol (z w : A) : (- z) * (- w) == z * w.
Proof.
  rewrite (comm_r (- z) w).
  rewrite (comm_l z w).
  rewrite (invol (z * w)).
  reflexivity. Qed.

End Context.

(** ** Noncommutative Unital Ring *)

Class IsRing (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) (y : A) (m : A -> A -> A) : Prop := {
  ring_add_is_grp :> IsGrp X x f k;
  ring_add_is_comm_bin_op :> IsCommBinOp X k;
  ring_mul_is_mon :> IsMon X y m;
  ring_is_distr :> IsDistr X m k;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) (y : A) (m : A -> A -> A)
  `{!IsRing X x f k y m}.

#[local] Instance ring_has_equiv_rel : HasEquivRel A := X.
#[local] Instance ring_has_zero : HasZero A := x.
#[local] Instance ring_has_neg : HasNeg A := f.
#[local] Instance ring_has_add : HasAdd A := k.
#[local] Instance ring_has_one : HasOne A := y.
#[local] Instance ring_has_mul : HasMul A := m.

Ltac note := progress (
  try change X with (equiv_rel (A := A)) in *;
  try change x with (zero (A := A)) in *;
  try change f with (neg (A := A)) in *;
  try change k with (add (A := A)) in *;
  try change y with (one (A := A)) in *;
  try change m with (mul (A := A)) in *).

(** Removing the unit element from a unital ring yields a nonunital ring. *)

#[export] Instance ring_is_rng : IsRng X x f k m.
Proof. esplit; typeclasses eauto. Qed.

(** Removing negation from a unital ring yields a unital semiring. *)

#[export] Instance ring_is_semiring : IsSemiring X x k y m.
Proof. esplit; typeclasses eauto. Qed.

Lemma ring_comm_unl_elem_l (z : A) : (- 1) * z == - z.
Proof with note.
  unsign...
  setoid_rewrite (comm_l 1 z).
  rewrite (unl_elem_l z).
  reflexivity. Qed.

Lemma ring_comm_unl_elem_r (z : A) : z * (- 1) == - z.
Proof with note.
  unsign...
  setoid_rewrite (comm_r z 1).
  rewrite (unl_elem_r z).
  reflexivity. Qed.

End Context.

(** ** Ring Homomorphism *)

Class IsRingHom (A B : Type)
  (X : A -> A -> Prop) (x : A) (f : A -> A) (k : A -> A -> A)
  (y : A) (m : A -> A -> A)
  (Y : B -> B -> Prop) (z : B) (g : B -> B) (n : B -> B -> B)
  (w : B) (p : B -> B -> B)
  (h : A -> B) : Prop := {
  ring_hom_dom_is_grp : IsRing X x f k y m;
  ring_hom_codom_is_grp : IsRing Y z g n w p;
  ring_hom_add_is_bin_pres :> IsBinPres Y k n h;
  ring_hom_mul_is_bin_pres :> IsBinPres Y m p h;
  ring_hom_mul_is_null_pres :> IsNullPres Y y w h;
  ring_hom_is_proper :> IsProper (X ==> Y) h;
}.
