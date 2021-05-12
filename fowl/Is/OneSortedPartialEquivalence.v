(* bad *)
From Coq Require Import
  Setoid Morphisms RelationClasses.
From Maniunfold.Has Require Export
  OneSortedEquivalenceRelation.
From Maniunfold.Is Require Export
  Symmetric Transitive.

Class IsPartEq (A : Type) `(HasEqRel A) : Prop := {
  A_eq_rel_is_sym :> IsSym eq_rel;
  A_eq_rel_is_trans :> IsTrans eq_rel;
}.

Section Context.

Context (A : Type) `{IsPartEq A}.

Global Instance eq_rel_p_e_r : PER eq_rel | 0.
Proof. split; typeclasses eauto. Defined.

End Context.
