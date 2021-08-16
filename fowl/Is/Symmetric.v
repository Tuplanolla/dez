(** * Symmetry *)

From DEZ Require Export
  Init.

(** ** Symmetric Binary Relation *)

Fail Fail Class IsSym (A : Type) (R : A -> A -> Prop) : Prop :=
  sym (x y : A) (a : R x y) : R y x.

Notation IsSym := Symmetric.
Notation sym := (symmetry : IsSym _).

From DEZ.Is Require Export
  Commutative.

Lemma specialization (A : Type) (R : A -> A -> Prop) :
  IsSym R <-> IsComm impl R.
Proof.
  split.
  - intros ? x y a. apply sym. apply a.
  - intros ? x y a. apply (comm (R := impl)). apply a. Qed.
