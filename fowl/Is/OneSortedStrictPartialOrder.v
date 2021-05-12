(* bad *)
From Coq Require Import
  Classes.RelationClasses.
From Maniunfold.Has Require Export
  OneSortedOrderRelation.
From Maniunfold.Is Require Export
  Irreflexive Transitive.
From Maniunfold.ShouldHave Require Import
  OneSortedOrderRelationNotations.

Class IsStrPartOrd (A : Type) `(HasOrdRel A) : Prop := {
  A_ord_rel_is_irrefl :> IsIrrefl ord_rel;
  A_ord_rel_is_trans :> IsTrans ord_rel;
}.

Section Context.

Context (A : Type) `{IsStrPartOrd A}.

Global Instance ord_rel_asymmetric : StrictOrder ord_rel | 0.
Proof. split; typeclasses eauto. Defined.

End Context.
