(** * Equivalence *)

From DEZ.Has Require Export
  EquivalenceRelation.
From DEZ.Is Require Export
  Reflexive Symmetric Transitive.
From DEZ.ShouldHave Require Import
  EquivalenceRelationNotations.

Fail Fail Class IsEq (A : Type) (HR : HasEqRel A) : Prop := {
  is_refl :> IsRefl _==_;
  is_sym :> IsSym _==_;
  is_trans :> IsTrans _==_;
}.

Notation IsEq := Equivalence.
