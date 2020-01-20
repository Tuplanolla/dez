From Maniunfold.Has Require Export
  EquivalenceRelation.
From Maniunfold.Is Require Export
  Symmetric.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations.

Class IsSymEq {A : Type} (has_eq_rel : HasEqRel A) : Prop :=
  sym_eq : forall x y : A, x == y -> y == x.

Section Context.

Context {A : Type} `{is_sym_eq : IsSymEq A}.

Global Instance eq_rel_is_sym : IsSym eq_rel := {}.
Proof. apply sym_eq. Qed.

End Context.
