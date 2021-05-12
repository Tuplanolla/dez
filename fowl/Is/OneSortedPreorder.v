From Maniunfold.Has Require Export
  OneSortedOrderRelation.
From Maniunfold.ShouldHave Require Export
  OneSortedOrderRelationNotations.
From Maniunfold.Is Require Export
  Reflexive Transitive.

Class IsPreord (A : Type) `(HasOrdRel A) : Prop := {
  ord_rel_reflexive :> Reflexive _<=_;
  ord_rel_transitive :> Transitive _<=_;
}.

Section Context.

Context (A : Type) `(IsPreord A).

Global Instance ord_rel_pre_order : PreOrder ord_rel | 0.
Proof. split; typeclasses eauto. Defined.

End Context.
