(** * Comonotonicity of a Function *)

From Maniunfold.Has Require Export
  OrderRelation.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations.

Fail Fail Class IsComono (A B : Type)
  (R : HasOrdRel A) (S : HasOrdRel B) (f : A -> B) : Prop :=
  comono (x y : A) (l : f x <= f y) : x <= y.

Notation IsComono R S := (Proper (R <== S)).
Notation comono := (proper_prf : IsComono _ _ _).
