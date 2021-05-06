From Maniunfold.Has Require Export
  Function OrderRelation.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations.

Class IsMono (A B : Type)
  `(!HasOrdRel A) `(!HasOrdRel B) `(!HasFn A B) : Prop :=
  mono (x y : A) (l : x <= y) : fn x <= fn y.

Instance proper `(IsMono) : Proper (_<=_ ==> _<=_) fn.
Proof. exact mono. Qed.
