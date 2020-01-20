From Maniunfold.Has Require Export
  EquivalenceRelation.
From Maniunfold.Is Require Export
  Transitive.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations.

Class IsTransEq {A : Type} (has_eq_rel : HasEqRel A) : Prop :=
  transitive_equivalence : forall x y z : A, x == y -> y == z -> x == z.

Section Context.

Context {A : Type} `{is_trans_eq : IsTransEq A}.

Global Instance trans_eq_is_trans : IsTrans eq_rel := {}.
Proof. apply transitive_equivalence. Qed.

End Context.
