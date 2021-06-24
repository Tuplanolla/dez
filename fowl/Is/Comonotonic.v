(** * Comonotonicity and Strict Comonotonicity of a Function *)

From Maniunfold.Has Require Export
  OrderRelations.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations.

Fail Fail Class IsComono (A B : Type)
  (HRA : HasOrdRel A) (HRB : HasOrdRel B) (f : A -> B) : Prop :=
  comono (x y : A) (a : f x <= f y) : x <= y.

Notation IsComono HRA HRB := (Proper (HRA <== HRB)).
Notation comono := (proper_prf : IsComono _ _ _).

(** Strict comonotonicity of an order relation is just
    comonotonicity of a strict order relation. *)

Notation IsStrComono HRA HRB := (Proper (HRA <== HRB)) (only parsing).
Notation str_comono := (proper_prf : IsStrComono _ _ _) (only parsing).
