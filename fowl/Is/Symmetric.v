(** * Symmetry *)

(* From DEZ.Is Require Export
  Commutative. *)
From DEZ Require Export
  Init.

(** ** Symmetric Binary Relation *)

Fail Fail Class IsSym (A : Type) (X : A -> A -> Prop) : Prop :=
  sym (x y : A) (a : X x y) : X y x.

Arguments symmetry {_ _ _} _ _ _.

Notation IsSym := Symmetric.
Notation sym := symmetry.

(** TODO Reinstate this. *)

(* Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** Symmetry is just a special case of commutativity. *)

#[local] Instance is_sym `{!IsComm impl X} : IsSym X.
Proof. intros x y. exact (comm x y). Qed.

#[local] Instance is_comm `{!IsSym X} : IsComm impl X.
Proof. intros x y. exact (sym x y). Qed.

End Context. *)
