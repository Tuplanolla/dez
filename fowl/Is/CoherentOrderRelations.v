From Maniunfold.Has Require Export
  OneSortedOrderRelation StrictOrderRelation.
From Maniunfold.ShouldHave Require Import
  OneSortedOrderRelationNotations OneSortedStrictOrderRelationNotations.

Class IsCohOrdRels (A : Type) `(HasOrdRel A) `(HasStrictOrdRel A) : Prop :=
  coh_ord_rels (x y : A) : x < y <-> x <= y /\ x <> y.
