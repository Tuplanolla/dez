(** * Connexity *)

From DEZ.Is Require Export
  Commutative.

(** ** Connected Binary Relation *)
(** ** Connex Binary Relation *)
(** ** Total Binary Relation *)

(** This definition has the same shape as [Nat.le_ge_cases]. *)

Class IsConnex (A : Type) (X : A -> A -> Prop) : Prop :=
  connex (x y : A) : X x y \/ X y x.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** Connexity implies commutativity up to disjunction. *)

#[export] Instance connex_is_comm_or `{!IsConnex X} : IsComm _\/_ X.
Proof. auto. Qed.

(** Commutativity up to disjunction implies connexity. *)

#[local] Instance comm_or_is_connex `{!IsComm _\/_ X} : IsConnex X.
Proof. auto. Qed.

End Context.
