From DEZ.Has Require Export
  Reciprocation.
From DEZ.Has Require Export
  Decidability.
From DEZ.Is Require Export
  Group Semigroup Monoid Semiring Ring.

Ltac ecrush :=
  hnf in *; repeat match goal with
  | |- exists _ : unit, _ => exists tt
  | |- forall _ : unit, _ => intros ?
  | x : unit |- _ => destruct x
  end; eauto.

Equations tt1 (x : unit) : unit :=
  tt1 _ := tt.

Equations tt2 (x y : unit) : unit :=
  tt2 _ _ := tt.

#[local] Instance unit_is_contr : IsContr unit.
Proof. ecrush. Qed.

Fail Fail Scheme Equality for unit.

Equations unit_eq_dec (x y : unit) : {x = y} + {x <> y} :=
  unit_eq_dec x y := left (irrel x y).

#[local] Instance unit_has_eq_dec : HasEqDec unit := unit_eq_dec.
#[local] Instance unit_has_eq_rel : HasEqRel unit := eq.

#[local] Instance unit_has_null_op : HasNullOp unit := tt.
#[local] Instance unit_has_un_op : HasUnOp unit := tt1.
#[local] Instance unit_has_bin_op : HasBinOp unit := tt2.

#[local] Instance is_assoc : IsAssoc eq tt2.
Proof. ecrush. Qed.

#[local] Instance is_semigrp : IsSemigrp eq tt2.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance is_comm : IsComm eq tt2.
Proof. ecrush. Qed.

#[local] Instance is_unl_l : IsUnlL eq tt tt2.
Proof. ecrush. Qed.

#[local] Instance is_unl_r : IsUnlR eq tt tt2.
Proof. ecrush. Qed.

#[local] Instance is_unl_l_r : IsUnlLR eq tt tt2.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance is_mon : IsMon eq tt tt2.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance is_inv_l : IsInvL eq tt tt1 tt2.
Proof. ecrush. Qed.

#[local] Instance is_inv_r : IsInvR eq tt tt1 tt2.
Proof. ecrush. Qed.

#[local] Instance is_inv_l_r : IsInvLR eq tt tt1 tt2.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance is_grp : IsGrp eq tt tt1 tt2.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance unit_has_zero : HasZero unit := tt.
#[local] Instance unit_has_neg : HasNeg unit := tt1.
#[local] Instance unit_has_add : HasAdd unit := tt2.
#[local] Instance unit_has_one : HasOne unit := tt.
#[local] Instance unit_has_recip : HasRecip unit := tt1.
#[local] Instance unit_has_mul : HasMul unit := tt2.

#[local] Instance is_distr_l : IsDistrL eq tt2 tt2.
Proof. ecrush. Qed.

#[local] Instance is_distr_r : IsDistrR eq tt2 tt2.
Proof. ecrush. Qed.

#[local] Instance is_distr_l_r : IsDistrLR eq tt2 tt2.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance is_absorb_elem_l : IsAbsorbElemL eq tt tt2.
Proof. ecrush. Qed.

#[local] Instance is_absorb_elem_r : IsAbsorbElemR eq tt tt2.
Proof. ecrush. Qed.

#[local] Instance is_absorb_elem_l_r : IsAbsorbElemLR eq tt tt2.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance is_semiring : IsSemiring eq tt tt2 tt tt2.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance is_ring : IsRing eq tt tt1 tt2 tt tt2.
Proof. esplit; typeclasses eauto. Qed.
