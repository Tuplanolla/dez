From Maniunfold.Has Require Export
  OrderRelationPackage.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations StrictOrderRelationNotations.

Class IsOrdRelPack (A : Type) `(HasOrdRelPack A) : Prop :=
  coh_ord_rels (x y : A) : x < y <-> x <= y /\ x <> y.
