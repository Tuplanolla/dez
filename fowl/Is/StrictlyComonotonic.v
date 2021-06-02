(* bad *)
From Maniunfold.Has Require Export
  Function.
From Maniunfold.ShouldHave Require Import
  OneSortedOrderRelationNotations OneSortedStrictOrderRelationNotations.
From Maniunfold.Is Require Export
  Monotonic CoherentOrderRelations.

Fail Fail Class IsStrictComono (A B : Type)
  `(HasStrictOrdRel A) `(HasStrictOrdRel B) `(HasFn A B) : Prop :=
  strict_comono (x y : A) (l : fn x < fn y) : x < y.

Notation IsStrictComono strict_ord_rel strict_ord_rel' fn :=
  (Proper (strict_ord_rel <== strict_ord_rel') fn).
Notation strict_comono :=
  (proper_prf (R := strict_ord_rel <== strict_ord_rel) (m := fn)).
