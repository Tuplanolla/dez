From Maniunfold.Has Require Export
  Function OneSortedOrderRelation.
From Maniunfold.ShouldHave Require Import
  OneSortedOrderRelationNotations.

Fail Fail Class IsComono (A B : Type)
  `(HasOrdRel A) `(HasOrdRel B) `(HasFn A B) : Prop :=
  comono (x y : A) (l : fn x <= fn y) : x <= y.

Notation IsComono ord_rel ord_rel' fn := (Proper (ord_rel <== ord_rel') fn).
Notation comono := (proper_prf (R := ord_rel <== ord_rel) (m := fn)).
