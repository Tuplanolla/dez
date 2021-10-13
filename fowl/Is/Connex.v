(** * Connexity *)

From DEZ.Is Require Export
  Commutative.

(** ** Connected Binary Relation *)
(** ** Connex Binary Relation *)
(** ** Total Binary Relation *)

Fail Fail Class IsConnex (A : Type) (R : A -> A -> Prop) : Prop :=
  is_comm :> IsComm _\/_ R.

(** This has the same shape as [le_ge_cases]. *)

Class IsConnex (A : Type) (R : A -> A -> Prop) : Prop :=
  connex (x y : A) : R x y \/ R y x.

Section Context.

Context (A : Type) (R : A -> A -> Prop).

(** Connexity is just a special case of commutativity. *)

#[local] Instance is_connex `(!IsComm _\/_ R) : IsConnex R.
Proof. intros x y. exact (comm x y). Qed.

#[local] Instance is_comm `(!IsConnex R) : IsComm _\/_ R.
Proof. intros x y. exact (connex x y). Qed.

End Context.

#[export] Hint Resolve is_connex : typeclass_instances.
