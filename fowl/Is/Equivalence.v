(** * Equivalence *)

From Maniunfold.Has Require Export
  EquivalenceRelation.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations.
From Maniunfold.Is Require Export
  Reflexive Symmetric Transitive.

Fail Fail Class IsEq (A : Type) (HR : HasEqRel A) : Prop := {
  is_refl :> IsRefl _==_;
  is_sym :> IsSym _==_;
  is_trans :> IsTrans _==_;
}.

Notation IsEq := Equivalence.
