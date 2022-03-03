From DEZ.Has Require Export
  Reciprocation.
From DEZ.Has Require Export
  Decisions.
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

#[local] Instance unit_is_contr : @IsContr unit eq.
Proof. ecrush. Qed.

#[local] Instance unit_is_prop : @IsProp unit eq.
Proof. ecrush. Qed.

Fail Fail Scheme Equality for unit.

Equations unit_equiv_dec (x y : unit) : {x = y} + {x <> y} :=
  unit_equiv_dec x y := left (irrel x y).

#[local] Instance unit_has_equiv_dec : HasEqDec unit := unit_equiv_dec.
#[local] Instance unit_has_equiv_rel : HasEquivRel unit := eq.

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

#[export] Hint Resolve unit_is_contr unit_has_equiv_dec unit_has_equiv_rel
  unit_has_null_op unit_has_un_op unit_has_bin_op is_assoc is_semigrp is_comm
  is_unl_l is_unl_r is_unl_l_r is_mon is_inv_l is_inv_r is_inv_l_r is_grp
  unit_has_zero unit_has_neg unit_has_add unit_has_one unit_has_recip
  unit_has_mul is_distr_l is_distr_r is_distr_l_r is_absorb_elem_l
  is_absorb_elem_r is_absorb_elem_l_r is_semiring is_ring :
  typeclass_instances.
