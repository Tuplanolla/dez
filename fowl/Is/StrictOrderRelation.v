From Maniunfold.Has Require Export
  Function StrictOrderRelation.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations StrictOrderRelationNotations.
From Maniunfold.Is Require Export
  Monotonic.

Class IsStrictMono (A B : Type)
  `(HasStrictOrdRel A) `(HasStrictOrdRel B) `(HasFn A B) : Prop :=
  strict_mono (x y : A) (l : x < y) : fn x < fn y.

Instance proper (A B : Type) `(IsStrictMono A B) : Proper (_<_ ==> _<_) fn.
Proof. exact strict_mono. Qed.

(** Strict monotonicity implies monotonicity. *)

(** TODO Add hypotheses to the predicative classes. *)

Class IsCohOrdRel (A : Type) `(HasOrdRel A) `(HasStrictOrdRel A) : Prop :=
  coh_ord_rel (x y : A) : x < y <-> x <= y /\ x <> y.

Instance is_mono (A B : Type)
  `(EqDec A) `(IsStrictMono A B)
  `(HasOrdRel A) `(HasOrdRel B) `(!Reflexive _<_)
  `(!IsCohOrdRel (A := A) _<=_ _<_) `(!IsCohOrdRel (A := B) _<=_ _<_) :
  IsMono _<_ _<_ fn.
Proof.
  intros x y l.
  destruct (eq_dec x y) as [e | f].
  - subst y. reflexivity.
  - pose proof coh_ord_rel x y as c.
    destruct c as [c0 c1].
    pose proof c1 ltac:(eauto).
    pose proof strict_mono x y ltac:(eauto).
    pose proof coh_ord_rel (fn x) (fn y) as d.
    destruct d as [d0 d1].
    pose proof d0 ltac:(eauto).
    eauto. Qed.

#[export] Hint Resolve proper is_mono : typeclass_instances.
