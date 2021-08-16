(** * Connexity *)

From DEZ Require Export
  Init.

(** ** Connected Binary Relation *)
(** ** Connex Binary Relation *)
(** ** Total Binary Relation *)

(** This has the same shape as [le_ge_cases]. *)

Class IsConnex (A : Type) (R : A -> A -> Prop) : Prop :=
  connex (x y : A) : R x y \/ R y x.

From DEZ.Is Require Export
  Commutative.

Lemma specialization (A : Type) (R : A -> A -> Prop) :
  IsConnex R <-> IsComm or R.
Proof.
  split.
  - intros ? x y. apply connex.
  - intros ? x y. apply (comm (R := or)). Qed.
