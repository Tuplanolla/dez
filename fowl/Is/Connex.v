(** * Connexity *)

From DEZ.Is Require Export
  Commutative.

(** ** Connected Binary Relation *)
(** ** Connex Binary Relation *)
(** ** Total Binary Relation *)

(** This has the same shape as [Z.le_ge_cases]. *)

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

(** ** Complete Binary Relation *)
(** ** Strictly Connex Binary Relation *)
(** ** Strongly Connected Binary Relation *)

(** This has the same shape as [Z.lt_trichotomy]. *)

Class IsStrConnex (A : Type) (X Y : A -> A -> Prop) : Prop :=
  str_connex (x y : A) : Y x y \/ X x y \/ Y y x.

Section Context.

Context (A : Type) (X Y : A -> A -> Prop).

(** Connexity implies strict connexity. *)

#[export] Instance connex_is_str_connex `{!IsConnex Y} : IsStrConnex X Y.
Proof.
  intros x y. destruct (connex x y) as [a | b].
  - auto.
  - auto. Qed.

End Context.
