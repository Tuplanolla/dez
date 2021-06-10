(** * Strict Monotonicity of a Function *)

From Maniunfold.Has Require Export
  StrictOrderRelation OrderRelation.
From Maniunfold.ShouldHave Require Import
  StrictOrderRelationNotations OrderRelationNotations.
From Maniunfold.Is Require Export
  Preorder CoherentOrderRelations Monotonic.

Fail Fail Class IsStrComono (A B : Type)
  (R : HasStrOrdRel A) (S : HasStrOrdRel B) (f : A -> B) : Prop :=
  str_comono (x y : A) (l : f x < f y) : x < y.

Notation IsStrComono R S := (Proper (R <== S)).
Notation str_comono := (proper_prf : IsStrComono _ _ _).
