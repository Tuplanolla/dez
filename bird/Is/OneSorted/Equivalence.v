(* bad *)
From Coq Require Import
  Setoid Morphisms.
From Maniunfold.Has Require Export
  OneSorted.EquivalenceRelation.
From Maniunfold.Is Require Export
  PartialEquivalence Reflexive.

Class IsEq (A : Type) (A_has_eq_rel : HasEqRel A) : Prop := {
  A_eq_rel_is_part_eq :> IsPartEq A eq_rel;
  A_eq_rel_is_refl :> IsRefl A eq_rel;
}.

Section Context.

Context {A : Type} `{is_eq : IsEq A}.

Global Instance eq_rel_equivalence : Equivalence eq_rel | 0.
Proof. split; typeclasses eauto. Qed.

End Context.
