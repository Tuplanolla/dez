(** * Symmetry *)

From DEZ.Is Require Export
  Commutative.

(** ** Symmetric Binary Relation *)

Fail Fail Class IsSym (A : Type) (X : A -> A -> Prop) : Prop :=
  sym (x y : A) (a : X x y) : X y x.

Arguments symmetry {_ _ _} _ _ _.

Notation IsSym := Symmetric.
Notation sym := symmetry.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** Symmetry implies commutativity up to implication. *)

#[export] Instance sym_is_comm_impl `{!IsSym X} : IsComm impl X.
Proof. auto. Qed.

(** Commutativity up to implication implies symmetry. *)

#[local] Instance comm_impl_is_sym `{!IsComm impl X} : IsSym X.
Proof. auto. Qed.

End Context.
