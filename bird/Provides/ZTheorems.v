From Coq Require Import
  ZArith.
From Maniunfold.Is Require Export
  OneSorted.Equivalence
  OneSorted.Magma OneSorted.Semigroup OneSorted.Monoid OneSorted.Group
  TwoSorted.Isomorphism.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Global Instance Z_has_eq_rel : HasEqRel Z := Z.eq.

Global Instance Z_eq_is_refl : IsRefl Z.eq.
Proof. intros x. reflexivity. Qed.

Global Instance Z_eq_is_sym : IsSym Z.eq.
Proof. intros x y p. symmetry; auto. Qed.

Global Instance Z_eq_is_trans : IsTrans Z.eq.
Proof. intros x y z p q. transitivity y; auto. Qed.

Global Instance Z_eq_is_part_eq : IsPartEq Z.eq.
Proof. split; typeclasses eauto. Qed.

Global Instance Z_eq_is_eq : IsEq Z.eq.
Proof. split; typeclasses eauto. Qed.

(** This is the sign--parity isomorphism. *)

Definition Z_to_double_N (n : Z) : N :=
  match n with
  | Z0 => N0
  | Zpos p => Npos (xO p)
  | Zneg p => Npos (Pos.pred_double p)
  end.

Definition Z_of_double_N (n : N) : Z :=
  match n with
  | N0 => Z0
  | Npos p => match p with
    | xI q => Zneg (Pos.succ q)
    | xO q => Zpos q
    | xH => Zneg xH
    end
  end.

Global Instance Z_N_has_iso : HasIso Z N := (Z_to_double_N, Z_of_double_N).

Global Instance Z_N_is_iso : IsIso Z_N_has_iso.
Proof.
  split.
  - intros x. cbn. destruct x as [| p | p].
    + reflexivity.
    + reflexivity.
    + destruct p as [q | q |].
      * reflexivity.
      * cbn. rewrite (Pos.succ_pred_double q). reflexivity.
      * reflexivity.
  - intros x. destruct x as [| p].
    + reflexivity.
    + destruct p as [q | q |].
      * cbn. rewrite (Pos.pred_double_succ q). reflexivity.
      * reflexivity.
      * reflexivity. Qed.

Module Additive.

Global Instance Z_add_has_bin_op : HasBinOp Z := Z.add.

Global Instance Z_add_is_mag : IsMag Z.add.
Proof. Qed.

Global Instance Z_add_is_assoc : IsAssoc Z.add.
Proof. intros x y z. apply Z.add_assoc. Qed.

Global Instance Z_add_is_sgrp : IsSgrp Z.add.
Proof. split; typeclasses eauto. Qed.

Global Instance Z_has_null_op : HasNullOp Z := Z.zero.

Global Instance Z_add_zero_is_l_unl : IsLUnl Z.add Z.zero.
Proof. intros x. apply Z.add_0_l. Qed.

Global Instance Z_add_zero_is_r_unl : IsRUnl Z.add Z.zero.
Proof. intros x. apply Z.add_0_r. Qed.

Global Instance Z_add_zero_is_unl : IsUnl Z.add Z.zero.
Proof. split; typeclasses eauto. Qed.

Global Instance Z_add_zero_is_mon : IsMon Z.add Z.zero.
Proof. split; typeclasses eauto. Qed.

Global Instance Z_has_un_op : HasUnOp Z := Z.opp.

Global Instance Z_add_zero_opp_is_l_inv : IsLInv Z.add Z.zero Z.opp.
Proof. intros x. apply Z.add_opp_diag_l. Qed.

Global Instance Z_add_zero_opp_is_r_inv : IsRInv Z.add Z.zero Z.opp.
Proof. intros x. apply Z.add_opp_diag_r. Qed.

Global Instance Z_add_zero_opp_is_inv : IsInv Z.add Z.zero Z.opp.
Proof. split; typeclasses eauto. Qed.

Global Instance Z_add_zero_opp_is_grp : IsGrp Z.add Z.zero Z.opp.
Proof. split; typeclasses eauto. Qed.

End Additive.

Module Multiplicative.

Global Instance Z_mul_has_bin_op : HasBinOp Z := Z.mul.

Global Instance Z_mul_is_mag : IsMag Z.mul.
Proof. Qed.

Global Instance Z_mul_is_assoc : IsAssoc Z.mul.
Proof. intros x y z. apply Z.mul_assoc. Qed.

Global Instance Z_mul_is_sgrp : IsSgrp Z.mul.
Proof. split; typeclasses eauto. Qed.

Global Instance Z_has_null_op : HasNullOp Z := Z.one.

Global Instance Z_mul_one_is_l_unl : IsLUnl Z.mul Z.one.
Proof. intros x. apply Z.mul_1_l. Qed.

Global Instance Z_mul_one_is_r_unl : IsRUnl Z.mul Z.one.
Proof. intros x. apply Z.mul_1_r. Qed.

Global Instance Z_mul_one_is_unl : IsUnl Z.mul Z.one.
Proof. split; typeclasses eauto. Qed.

Global Instance Z_mul_one_is_mon : IsMon Z.mul Z.one.
Proof. split; typeclasses eauto. Qed.

End Multiplicative.
