(** * Connexity *)

From DEZ.Is Require Export
  Commutative.

(** ** Connected Binary Relation *)
(** ** Connex Binary Relation *)
(** ** Total Binary Relation *)

Fail Fail Class IsConnex (A : Type) (X : A -> A -> Prop) : Prop :=
  is_comm :> IsComm _\/_ X.

(** This has the same shape as [le_ge_cases]. *)

Class IsConnex (A : Type) (X : A -> A -> Prop) : Prop :=
  connex (x y : A) : X x y \/ X y x.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** Connexity is just a special case of commutativity. *)

#[local] Instance is_connex `(!IsComm _\/_ X) : IsConnex X.
Proof. intros x y. exact (comm x y). Qed.

#[local] Instance is_comm `(!IsConnex X) : IsComm _\/_ X.
Proof. intros x y. exact (connex x y). Qed.

End Context.

#[export] Hint Resolve is_connex : typeclass_instances.
