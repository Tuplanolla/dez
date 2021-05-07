From Maniunfold.Has Require Export
  Function OrderRelation.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations.

Class IsMono (A B : Type)
  `(!HasOrdRel A) `(!HasOrdRel B) `(!HasFn A B) : Prop :=
  mono (x y : A) (l : x <= y) : fn x <= fn y.

(** Monotonicity is a special case of respectfulness. *)

#[local] Instance is_mono (A B : Type)
  `(HasOrdRel A) `(HasOrdRel B) `(HasFn A B)
  `(!Proper (_<=_ ==> _<=_) fn) : IsMono _<=_ _<=_ fn.
Proof. eassumption. Qed.

#[export] Hint Resolve is_mono : typeclass_instances.
