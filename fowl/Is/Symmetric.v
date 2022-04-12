(** * Symmetry *)

From Coq Require Import
  Classes.RelationClasses.
From DEZ.Is Require Export
  Commutative.

(** ** Symmetric Binary Relation *)

Fail Fail Class IsSym (A : Type) (X : A -> A -> Prop) : Prop :=
  sym (x y : A) (a : X x y) : X y x.

Arguments Symmetric {_} _.
Arguments symmetry {_ _ _} _ _ _.

Notation IsSym := Symmetric.
Notation sym := symmetry.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** Symmetry is a special case of commutativity up to implication. *)

#[local] Instance sym_is_comm_form_impl `{!IsSym X} : IsCommForm impl X.
Proof. auto. Qed.

#[local] Instance comm_form_impl_is_sym `{!IsCommForm impl X} : IsSym X.
Proof. auto. Qed.

End Context.
