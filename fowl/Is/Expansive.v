(** * Expansivity *)

From DEZ.Has Require Export
  Distance OrderRelations.
From DEZ.ShouldHave Require Import
  OrderRelationNotations.

(** ** Expansive Function *)
(** ** Long Map *)

Class IsExpand (A B C : Type)
  (HR : HasOrdRel C) (HdA : HasDist C A) (HdB : HasDist C B)
  (f : A -> B) : Prop :=
  expand (x y : A) : dist x y <= dist (f x) (f y).

(** TODO Dualize [IsContract]. *)
