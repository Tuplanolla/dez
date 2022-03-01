(** * Comonotonicity and Strict Comonotonicity of a Function *)

From DEZ.Has Require Export
  OrderRelations.
From DEZ.Supports Require Import
  OrderNotations.

Class IsComono (A B : Type)
  (HRA : HasOrdRel A) (HRB : HasOrdRel B) (f : A -> B) : Prop :=
  comono (x y : A) (a : f x <= f y) : x <= y.

(** Strict comonotonicity of an order relation is just
    comonotonicity of a strict order relation. *)

Notation IsStrComono := IsComono (only parsing).
Notation str_comono := (comono : IsStrComono _ _ _) (only parsing).
