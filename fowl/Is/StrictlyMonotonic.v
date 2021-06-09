(** * Strict Monotonicity of a Function *)

From Maniunfold.Has Require Export
  StrictOrderRelation OrderRelation.
From Maniunfold.ShouldHave Require Import
  StrictOrderRelationNotations OrderRelationNotations.
From Maniunfold.Is Require Export
  Preorder CoherentOrderRelations Monotonic.

Fail Fail Class IsStrMono (A B : Type)
  (R : HasStrOrdRel A) (S : HasStrOrdRel B) (f : A -> B) : Prop :=
  str_mono (x y : A) (l : x < y) : f x < f y.

Notation IsStrMono R S f := (Proper (R ==> S) f).
Notation str_mono := (proper_prf : IsStrMono _ _ _).

Section Context.

Context (A B : Type)
  `(RA : HasOrdRel A) `(!IsPreord RA)
  `(SA : HasStrOrdRel A) `(!IsCohOrdRels RA SA) `(EqDec A)
  `(RB : HasOrdRel B) `(!IsPreord RB)
  `(SB : HasStrOrdRel B) `(!IsCohOrdRels RB SB) (f : A -> B).

(** Strict monotonicity implies monotonicity. *)

#[local] Instance is_mono `(!IsStrMono _<_ _<_ f) : IsMono _<=_ _<=_ f.
Proof.
  intros x y lxy.
  destruct (eq_dec x y) as [exy | fxy].
  - rewrite exy. reflexivity.
  - pose proof proj2 (coh_ord_rels x y) (conj lxy fxy) as lxy'.
    pose proof str_mono x y ltac:(eauto) as lfxy'.
    destruct (proj1 (coh_ord_rels (f x) (f y)) lfxy') as [lfxy ffxy].
    apply lfxy. Qed.

End Context.

#[export] Hint Resolve is_mono : typeclass_instances.
