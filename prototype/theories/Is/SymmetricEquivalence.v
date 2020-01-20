From Maniunfold.Has Require Export
  EquivalenceRelation.
From Maniunfold.Is Require Export
  Symmetric.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations.

Class IsSymEq {A : Type} (has_eq_rel : HasEqRel A) : Prop :=
  symmetric_equivalence : forall x y : A, x == y -> y == x.

Section Context.

Context {A : Type} `{is_sym_eq : IsSymEq A}.

Global Instance sym_eq_is_sym : IsSym eq_rel := {}.
Proof. apply symmetric_equivalence. Qed.

End Context.
