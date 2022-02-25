(** * Group Structure *)

From DEZ.Has Require Export
  EquivalenceRelation Zero Addition One Multiplication.
From DEZ.Is Require Export
  Monoid Commutative Distributive Absorbing Truncated.
From DEZ.ShouldHave Require Import
  EquivalenceNotations ArithmeticNotations.

(** ** Semiring *)

Class IsSemiring (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) (y : A) (m : A -> A -> A) : Prop := {
  add_is_mon :> IsMon X x k;
  add_is_comm :> IsComm X k;
  mul_is_mon :> IsMon X y m;
  is_distr_l_r :> IsDistrLR X m k;
  is_absorb_elem_l_r :> IsAbsorbElemLR X x m;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) (y : A) (m : A -> A -> A)
  `(!IsSemiring X x k y m).

#[local] Instance has_equiv_rel : HasEquivRel A := X.
#[local] Instance has_zero : HasZero A := x.
#[local] Instance has_add : HasAdd A := k.
#[local] Instance has_one : HasOne A := y.
#[local] Instance has_mul : HasMul A := m.

Ltac note := progress (
  try change X with equiv_rel in *;
  try change x with zero in *;
  try change k with add in *;
  try change y with one in *;
  try change m with mul in *).

(** TODO Does this make sense anymore? *)

Import Zero.Subclass Negation.Subclass Addition.Subclass
  One.Subclass Multiplication.Subclass.

Ltac subclass := progress (
  try change bin_rel with equiv_rel in *;
  try change null_op with zero in *;
  try change bin_op with add in *;
  try change null_op with one in *;
  try change bin_op with mul in *).

#[local] Instance is_contr (a : X 0 1) : IsContr X.
Proof.
  hnf.
  note.
  exists 0.
  intros z.
  assert (b : z * 0 == z * 1).
  { apply (proper : IsProper (_==_ ==> _==_ ==> _==_) _*_); easy. }
  setoid_rewrite (unl_r z) in b.
  setoid_rewrite (absorb_elem_r z) in b.
  setoid_rewrite b.
  reflexivity. Qed.

End Context.

#[export] Hint Resolve is_contr : typeclass_instances.
