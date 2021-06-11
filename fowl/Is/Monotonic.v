(** * Monotonicity and Strict Monotonicity of a Function *)

From Maniunfold.Has Require Export
  Decidability StrictOrderRelation OrderRelation.
From Maniunfold.ShouldHave Require Import
  StrictOrderRelationNotations OrderRelationNotations.
From Maniunfold.Is Require Export
  Preorder CoherentOrderRelations.

Fail Fail Class IsMono (A B : Type)
  (RA : HasOrdRel A) (RB : HasOrdRel B) (f : A -> B) : Prop :=
  mono (x y : A) (l : x <= y) : f x <= f y.

Notation IsMono RA RB := (Proper (RA ==> RB)).
Notation mono := (proper_prf : IsMono _ _ _).

(** Strict monotonicity of an order relation is just
    monotonicity of a strict order relation. *)

Notation IsStrMono RA RB := (Proper (RA ==> RB)) (only parsing).
Notation str_mono := (proper_prf : IsMono _ _ _) (only parsing).

(** Decidable strict monotonicity implies monotonicity. *)

Section Context.

Context (A B : Type) (d : HasEqDec A)
  (RA : HasOrdRel A) `(!IsPreord RA)
  (SA : HasStrOrdRel A) `(!IsCohOrdRels RA SA)
  (RB : HasOrdRel B) `(!IsPreord RB)
  (SB : HasStrOrdRel B) `(!IsCohOrdRels RB SB)
  (f : A -> B) `(!IsMono _<_ _<_ f).

#[local] Instance is_mono : IsMono _<=_ _<=_ f.
Proof.
  intros x y lxy.
  decide (x = y) as [exy | fxy].
  - rewrite exy. reflexivity.
  - pose proof proj2 (coh_ord_rels x y) (conj lxy fxy) as lxy'.
    pose proof str_mono x y ltac:(eauto) as lfxy'.
    destruct (proj1 (coh_ord_rels (f x) (f y)) lfxy') as [lfxy ffxy].
    apply lfxy. Qed.

End Context.

#[export] Hint Resolve is_mono : typeclass_instances.
