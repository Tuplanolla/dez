(** * Idempotency of an Element and a Binary Operation and a Function *)

From Maniunfold.Has Require Export
  BinaryOperation.
From Maniunfold.Is Require Export
  FunctionExtensionality.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

Class IsIdemElem (A : Type) (Hk : HasBinOp A) (x : A) : Prop :=
  idem_elem : x + x = x.

Class IsIdemBinOp (A : Type) (Hk : HasBinOp A) : Prop :=
  idem_bin_op (x : A) : x + x = x.

Section Context.

Context (A : Type) (Hk : HasBinOp A) `(!IsIdemBinOp _+_).

(** For an idempotent binary operation, every element is idempotent. *)

#[local] Instance is_idem_elem (x : A) : IsIdemElem _+_ x.
Proof. apply idem_bin_op. Qed.

End Context.

#[export] Hint Resolve is_idem_elem : typeclass_instances.

Class IsIdemFn (A : Type) (f : A -> A) : Prop :=
  idem_fn (x : A) : f (f x) = f x.

Section Context.

Context `(IsFunExt) (A : Type) (f : A -> A) `(!IsIdemFn f).

(** Idempotent functions are idempotent elements of the endofunction monoid. *)

#[local] Instance compose_is_idem_elem : IsIdemElem _o_ f.
Proof.
  apply fun_ext.
  intros x.
  unfold compose.
  setoid_rewrite idem_fn.
  reflexivity. Qed.

End Context.

#[export] Hint Resolve compose_is_idem_elem : typeclass_instances.
