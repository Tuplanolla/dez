From Maniunfold.Has Require Export
  Function OneSortedOrderRelation.
From Maniunfold.ShouldHave Require Import
  OneSortedOrderRelationNotations.

Fail Fail Class IsMono (A B : Type)
  `(HasOrdRel A) `(HasOrdRel B) `(HasFn A B) : Prop :=
  mono (x y : A) (l : x <= y) : fn x <= fn y.

Notation IsMono ord_rel ord_rel' := (Proper (ord_rel ==> ord_rel')).
Notation mono := (proper_prf (R := ord_rel ==> ord_rel) (m := fn)).
