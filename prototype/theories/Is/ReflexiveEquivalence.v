From Maniunfold.Has Require Export
  EquivalenceRelation.
From Maniunfold.Is Require Export
  Reflexive.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations.

Class IsReflEq {A : Type} (has_eq_rel : HasEqRel A) : Prop :=
  reflexive_equivalence : forall x : A, x == x.

Section Context.

Context {A : Type} `{is_refl_eq : IsReflEq A}.

Global Instance refl_eq_is_refl : IsRefl eq_rel := {}.
Proof. apply reflexive_equivalence. Qed.

End Context.
