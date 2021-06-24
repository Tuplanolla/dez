(** * Idempotency of an Element and a Binary Operation and a Function *)

From Maniunfold.Has Require Export
  BinaryOperation.
From Maniunfold.Is Require Export
  Extensional.
From Maniunfold.ShouldHave Require Import
  MultiplicativeNotations.

Class IsIdemElem (A : Type) (x : A) (Hk : HasBinOp A) : Prop :=
  idem_elem : x * x = x.

Class IsIdemBinOp (A : Type) (Hk : HasBinOp A) : Prop :=
  idem_bin_op (x : A) : x * x = x.

Section Context.

Context (A : Type) (Hk : HasBinOp A) `(!IsIdemBinOp _*_).

(** For an idempotent binary operation, every element is idempotent. *)

#[local] Instance is_idem_elem (x : A) : IsIdemElem x _*_.
Proof. apply idem_bin_op. Qed.

End Context.

#[export] Hint Resolve is_idem_elem : typeclass_instances.

Class IsIdem (A : Type) (f : A -> A) : Prop :=
  idem (x : A) : f (f x) = f x.

Section Context.

Context `(IsFunExt) (A : Type) (f : A -> A) `(!IsIdem f).

(** Idempotent functions are idempotent elements of the endofunction monoid. *)

#[local] Instance compose_is_idem_elem : IsIdemElem f _o_.
Proof.
  apply fun_ext.
  intros x.
  unfold compose.
  setoid_rewrite idem.
  reflexivity. Qed.

End Context.

#[export] Hint Resolve compose_is_idem_elem : typeclass_instances.
