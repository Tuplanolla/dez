(** * Monotonicity and Strict Monotonicity of a Function *)

From Maniunfold.Has Require Export
  Decidability OrderRelations.
From Maniunfold.Is Require Export
  Preorder CoherentOrderRelations.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations.

Fail Fail Class IsMono (A B : Type)
  (HRA : HasOrdRel A) (HRB : HasOrdRel B) (f : A -> B) : Prop :=
  mono (x y : A) (l : x <= y) : f x <= f y.

Notation IsMono HRA HRB := (Proper (HRA ==> HRB)).
Notation mono := (proper_prf : IsMono _ _ _).

(** Strict monotonicity of an order relation is just
    monotonicity of a strict order relation. *)

Notation IsStrMono HRA HRB := (Proper (HRA ==> HRB)) (only parsing).
Notation str_mono := (proper_prf : IsMono _ _ _) (only parsing).

Section Context.

Context (A B : Type) (d : HasEqDec A)
  (HRA : HasOrdRel A) `(!IsPreord HRA)
  (HSA : HasStrOrdRel A) `(!IsCohOrdRels HRA HSA)
  (HRB : HasOrdRel B) `(!IsPreord HRB)
  (HSB : HasStrOrdRel B) `(!IsCohOrdRels HRB HSB)
  (f : A -> B) `(!IsMono _<_ _<_ f).

(** Decidable strict monotonicity implies monotonicity. *)

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
