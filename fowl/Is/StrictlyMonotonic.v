From Maniunfold.Has Require Export
  Function.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations StrictOrderRelationNotations.
From Maniunfold.Is Require Export
  Monotonic CoherentOrderRelations.

Class IsStrictMono (A B : Type)
  `(HasStrictOrdRel A) `(HasStrictOrdRel B) `(HasFn A B) : Prop :=
  strict_mono (x y : A) (l : x < y) : fn x < fn y.

#[local] Instance is_strict_mono (A B : Type)
  `(HasStrictOrdRel A) `(HasStrictOrdRel B) `(HasFn A B)
  `(!Proper (_<_ ==> _<_) fn) : IsStrictMono _<_ _<_ fn.
Proof. eassumption. Qed.

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

#[export] Hint Resolve is_strict_mono is_mono : typeclass_instances.
