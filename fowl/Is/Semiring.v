(** * Group Structure *)

From DEZ.Has Require Export
  EquivalenceRelation Zero Addition One Multiplication.
From DEZ.Is Require Export
  Monoid Commutative Distributive Absorbing Truncated.
From DEZ.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations.

(** ** Semiring *)

Class IsSemiring (A : Type) (R : A -> A -> Prop)
  (x : A) (k : A -> A -> A) (y : A) (m : A -> A -> A) : Prop := {
  add_is_mon :> IsMon R x k;
  add_is_comm :> IsComm R k;
  mul_is_mon :> IsMon R y m;
  is_distr_l_r :> IsDistrLR R m k;
  is_absorb_elem_l_r :> IsAbsorbElemLR R x m;
}.

Class IsContrGen (A : Type) (R : A -> A -> Prop) : Prop :=
  contr_gen : exists x : A, forall y : A, R x y.

Section Context.

Context (A : Type) (R : A -> A -> Prop)
  (x : A) (k : A -> A -> A) (y : A) (m : A -> A -> A)
  `(!IsSemiring R x k y m).

#[local] Instance has_eq_rel : HasEqRel A := R.
#[local] Instance has_zero : HasZero A := x.
#[local] Instance has_add : HasAdd A := k.
#[local] Instance has_one : HasOne A := y.
#[local] Instance has_mul : HasMul A := m.

Ltac note := progress (
  change R with _==_ in *;
  change x with 0 in *;
  change k with _+_ in *;
  change y with 1 in *;
  change m with _*_ in *).

Import Zero.Subclass Negation.Subclass Addition.Subclass
  One.Subclass Multiplication.Subclass.

Ltac subclass := progress (
  try change bin_rel with eq_rel in *;
  try change null_op with zero in *;
  try change bin_op with add in *;
  try change null_op with one in *;
  try change bin_op with mul in *).

#[local] Instance is_contr (a : R 0 1) : IsContrGen R.
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
