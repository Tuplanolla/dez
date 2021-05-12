From Maniunfold.Has Require Export
  Function OneSortedOrderRelation.
From Maniunfold.ShouldHave Require Import
  OneSortedOrderRelationNotations.

Fail Fail Class IsMono (A B : Type)
  `(!HasOrdRel A) `(!HasOrdRel B) `(!HasFn A B) : Prop :=
  mono (x y : A) (l : x <= y) : fn x <= fn y.

Notation IsMono ord_rel ord_rel fn := (Proper (ord_rel ==> ord_rel) fn).
Notation mono := (_ : IsMono ord_rel ord_rel fn).
