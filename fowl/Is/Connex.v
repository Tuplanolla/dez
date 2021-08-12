(** * Properties of Binary Relations *)

From DEZ.Has Require Export
  BinaryRelation.
From DEZ.ShouldHave Require Import
  BinaryRelationNotations.

(** ** Connected Binary Relation *)
(** ** Connex Binary Relation *)
(** ** Total Binary Relation *)

(** This has the same shape as [le_ge_cases]. *)

Class IsConnex (A : Type) (HR : HasBinRel A) : Prop :=
  connex (x y : A) : x ~ y \/ y ~ x.
