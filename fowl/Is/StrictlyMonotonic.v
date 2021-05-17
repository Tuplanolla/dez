From Maniunfold.Has Require Export
  Function.
From Maniunfold.ShouldHave Require Import
  OneSortedOrderRelationNotations OneSortedStrictOrderRelationNotations.
From Maniunfold.Is Require Export
  Monotonic CoherentOrderRelations.

Fail Fail Class IsStrictMono (A B : Type)
  `(HasStrictOrdRel A) `(HasStrictOrdRel B) `(HasFn A B) : Prop :=
  strict_mono (x y : A) (l : x < y) : fn x < fn y.

Notation IsStrictMono strict_ord_rel strict_ord_rel' :=
  (Proper (strict_ord_rel ==> strict_ord_rel')).
Notation strict_mono :=
  (proper_prf (R := strict_ord_rel ==> strict_ord_rel) (m := fn)).

(** Strict monotonicity implies monotonicity. *)

Section Context.

Context (A B : Type)
  `(EqDec A) `(IsCohOrdRels A) `(!@PreOrder A _<=_)
  `(IsCohOrdRels B) `(!@PreOrder B _<=_)
  `(HasFn A B).

#[local] Instance is_mono `(!IsStrictMono _<_ _<_ fn) : IsMono _<=_ _<=_ fn.
Proof.
  intros x y l.
  destruct (eq_dec x y) as [e | f].
  - subst y. reflexivity.
  - pose proof proj2 (coh_ord_rels x y) ltac:(eauto) as l'.
    pose proof strict_mono x y ltac:(eauto) as lf'.
    destruct (proj1 (coh_ord_rels (fn x) (fn y)) ltac:(eauto)) as [lf ff].
    eauto. Qed.

End Context.

#[export] Hint Resolve is_mono : typeclass_instances.
