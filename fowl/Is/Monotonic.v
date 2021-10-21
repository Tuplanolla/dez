(** * Monotonicity and Strict Monotonicity of a Function and a Binary Operation *)

From DEZ.Has Require Export
  Decidability OrderRelations BinaryOperation.
From DEZ.Is Require Export
  Preorder CoherentOrderRelations.
From DEZ.ShouldHave Require Import
  OrderRelationNotations AdditiveNotations.

Fail Fail Class IsMono (A B : Type)
  (X : HasOrdRel A) (Y : HasOrdRel B) (f : A -> B) : Prop :=
  mono (x y : A) (a : x <= y) : f x <= f y.

Notation IsMono X Y := (Proper (X ==> Y)).
Notation mono := (proper_prf : IsMono _ _ _).

(** Strict monotonicity over an order relation is just
    monotonicity over a strict order relation. *)

Notation IsStrMono X Y := (Proper (X ==> Y)) (only parsing).
Notation str_mono := (proper_prf : IsMono _ _ _) (only parsing).

Section Context.

Context (A B : Type) (Hd : HasEqDec A)
  (HRA : HasOrdRel A) (HSA : HasStrOrdRel A) `(!IsCohOrdRels HRA HSA)
  (HRB : HasOrdRel B) (HSB : HasStrOrdRel B) `(!IsCohOrdRels HRB HSB)
 `(!IsPreord HRB) (f : A -> B) `(!IsMono _<_ _<_ f).

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

(** This has the same shape as [add_le_mono_l]. *)

Class IsMonoBinOpL (A : Type)
  (HR : HasOrdRel A) (Hk : HasBinOp A) : Prop :=
  mono_bin_op_l (x y z : A) (a : x <= y) : z + x <= z + y.

(** This has the same shape as [add_le_mono_r]. *)

Class IsMonoBinOpR (A : Type)
  (HR : HasOrdRel A) (Hk : HasBinOp A) : Prop :=
  mono_bin_op_r (x y z : A) (a : x <= y) : x + z <= y + z.

Fail Fail Class IsMonoBinOp (A : Type)
  (HR : HasOrdRel A) (Hk : HasBinOp A) : Prop :=
  mono_bin_op (x0 y0 : A) (a0 : x0 <= y0) (x1 y1 : A) (a1 : x1 <= y1) :
  x0 + x1 <= y0 + y1.

Notation IsMonoBinOp HR := (Proper (HR ==> HR ==> HR)).
Notation mono_bin_op := (proper_prf : IsMonoBinOp _ _).

Notation IsStrMonoBinOp HR := (Proper (HR ==> HR ==> HR)) (only parsing).
Notation str_mono_bin_op := (proper_prf : IsStrMonoBinOp _ _) (only parsing).

Module FromLR.

Section Context.

Context (A : Type) (HR : HasOrdRel A) (Hk : HasBinOp A)
  `(!IsPreord _<=_) `(!IsMonoBinOpL _<=_ _+_) `(!IsMonoBinOpR _<=_ _+_).

(** Left and right monotonicity of a binary relation imply its monotonicity. *)

#[local] Instance is_mono_bin_op : IsMonoBinOp _<=_ _+_.
Proof.
  intros x0 y0 a0 x1 y1 a1.
  transitivity (x0 + y1).
  - apply mono_bin_op_l. apply a1.
  - apply mono_bin_op_r. apply a0. Qed.

End Context.

#[export] Hint Resolve is_mono_bin_op : typeclass_instances.

End FromLR.

Section Context.

Context (A : Type) (HR : HasOrdRel A) (Hk : HasBinOp A)
  `(!IsPreord _<=_) `(!IsMonoBinOp _<=_ _+_).

(** Monotonicity of a binary relation implies its left monotonicity. *)

#[local] Instance is_mono_bin_op_l : IsMonoBinOpL _<=_ _+_.
Proof.
  intros x y z a.
  apply mono_bin_op.
  - reflexivity.
  - apply a. Qed.

(** Monotonicity of a binary relation implies its right monotonicity. *)

#[local] Instance is_mono_bin_op_r : IsMonoBinOpR _<=_ _+_.
Proof.
  intros x y z a.
  apply mono_bin_op.
  - apply a.
  - reflexivity. Qed.

End Context.

#[export] Hint Resolve is_mono_bin_op_l is_mono_bin_op_r : typeclass_instances.
