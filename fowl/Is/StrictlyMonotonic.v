(** * Strict Monotonicity of a Function *)

From Maniunfold.Has Require Export
  OneSortedOrderRelation.
From Maniunfold.ShouldHave Require Import
  OneSortedOrderRelationNotations OneSortedStrictOrderRelationNotations.
From Maniunfold.Is Require Export
  Monotonic CoherentOrderRelations.

Fail Fail Class IsStrictMono (A B : Type)
  (R : HasStrictOrdRel A) (S : HasStrictOrdRel B) (f : A -> B) : Prop :=
  strict_mono (x y : A) (l : x < y) : f x < f y.

Notation IsStrictMono R S f := (Proper (R ==> S) f).
Notation strict_mono := (proper_prf : IsStrictMono _ _ _).

Section Context.

Context (A B : Type) (f : A -> B)
  `(EqDec A) `(IsCohOrdRels A) `(!@PreOrder A _<=_)
  `(IsCohOrdRels B) `(!@PreOrder B _<=_)
  `(HasFn A B).

(** Strict monotonicity implies monotonicity. *)

#[local] Instance is_mono `(!IsStrictMono _<_ _<_ f) : IsMono _<=_ _<=_ f.
Proof.
  intros x y l.
  destruct (eq_dec x y) as [e | f'].
  - subst y. reflexivity.
  - pose proof proj2 (coh_ord_rels x y) ltac:(eauto) as l'.
    pose proof strict_mono x y ltac:(eauto) as lf'.
    destruct (proj1 (coh_ord_rels (fn x) (fn y)) ltac:(eauto)) as [lf ff].
    eauto. Qed.

End Context.

#[export] Hint Resolve is_mono : typeclass_instances.
