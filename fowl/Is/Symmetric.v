(** * Symmetry *)

From DEZ.Is Require Export
  Commutative.

(** ** Symmetric Binary Relation *)

Fail Fail Class IsSym (A : Type) (X : A -> A -> Prop) : Prop :=
  sym (x y : A) (a : X x y) : X y x.

Notation IsSym := Symmetric.
Notation sym := (@symmetry _ _ _ : IsSym _).

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** Symmetry is just a special case of commutativity. *)

#[local] Instance is_sym `(!IsComm impl X) : IsSym X.
Proof. intros x y. exact (comm x y). Qed.

#[local] Instance is_comm `(!IsSym X) : IsComm impl X.
Proof. intros x y. exact (sym x y). Qed.

End Context.

#[export] Hint Resolve is_sym : typeclass_instances.
