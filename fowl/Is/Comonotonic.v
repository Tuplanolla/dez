(** * Comonotonicity of a Function *)

From Maniunfold.Has Require Export
  Function OneSortedOrderRelation.
From Maniunfold.ShouldHave Require Import
  OneSortedOrderRelationNotations.

Fail Fail Class IsComono (A B : Type)
  (R : HasOrdRel A) (S : HasOrdRel B) (f : A -> B) : Prop :=
  comono (x y : A) (l : f x <= f y) : x <= y.

Notation IsComono R S f := (Proper (R <== S) f).
Notation comono := (proper_prf : IsComono _ _ _).
