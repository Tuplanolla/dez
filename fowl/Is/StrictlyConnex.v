(** * Strict Connexity or Strong Connectedness or Completeness of a Binary Relation *)

From DEZ Require Export
  Init.

(** This has the same shape as [lt_trichotomy]. *)

Class IsStrConnex (A : Type) (X Y : A -> A -> Prop) : Prop :=
  str_connex (x y : A) : Y x y \/ X x y \/ Y y x.
