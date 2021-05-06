From Maniunfold.Has Require Export
  Function.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations StrictOrderRelationNotations.
From Maniunfold.Is Require Export
  Monotonic OrderRelationPackage.

Class IsStrictMono (A B : Type)
  `(HasStrictOrdRel A) `(HasStrictOrdRel B) `(HasFn A B) : Prop :=
  strict_mono (x y : A) (l : x < y) : fn x < fn y.

Instance proper (A B : Type) `(IsStrictMono A B) : Proper (_<_ ==> _<_) fn.
Proof. exact strict_mono. Qed.

(** Strict monotonicity implies monotonicity. *)

Instance is_mono (A B : Type)
  `(EqDec A) `(IsOrdRelPack A) `(IsOrdRelPack B)
  `(HasFn A B) `(!IsStrictMono _<_ _<_ fn) `(!Reflexive (A := B) _<=_) :
  IsMono _<=_ _<=_ fn.
Proof.
  intros x y l.
  destruct (eq_dec x y) as [e | f].
  - subst y. reflexivity.
  - pose proof proj2 (coh_ord_rels x y) ltac:(eauto) as l'.
    pose proof strict_mono x y ltac:(eauto) as lf'.
    destruct (proj1 (coh_ord_rels (fn x) (fn y)) ltac:(eauto)) as [lf ff].
    eauto. Qed.

#[export] Hint Resolve proper is_mono : typeclass_instances.
