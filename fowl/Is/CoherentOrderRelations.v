From Maniunfold.Has Require Export
  OrderRelation StrictOrderRelation.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations StrictOrderRelationNotations.

Class IsCohOrdRels (A : Type) `(HasOrdRel A) `(HasStrictOrdRel A) : Prop :=
  coh_ord_rels (x y : A) : x < y <-> x <= y /\ x <> y.
