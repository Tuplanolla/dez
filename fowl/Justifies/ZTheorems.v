From Coq Require Import
  ZArith.ZArith.
From DEZ.Has Require Export
  Decisions.
From DEZ.Is Require Export
  Group Semigroup
  Monoid Semiring Ring
  Equivalence PartialEquivalence Isomorphism.

Ltac ecrush :=
  hnf in *; eauto with zarith.

#[local] Instance has_equiv_dec : HasEqDec Z := Z.eq_dec.
#[local] Instance has_equiv_rel : HasEquivRel Z := eq.

Module Additive.

#[local] Instance has_null_op : HasNullOp Z := Z.zero.
#[local] Instance has_un_op : HasUnOp Z := Z.opp.
#[local] Instance has_bin_op : HasBinOp Z := Z.add.

#[local] Instance is_assoc : IsAssoc eq Z.add.
Proof. ecrush. Qed.

#[local] Instance is_semigrp : IsSemigrp eq Z.add.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance is_unl_l : IsUnlL eq Z.zero Z.add.
Proof. ecrush. Qed.

#[local] Instance is_unl_r : IsUnlR eq Z.zero Z.add.
Proof. ecrush. Qed.

#[local] Instance is_unl : IsUnlLR eq Z.zero Z.add.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance is_mon : IsMon eq Z.zero Z.add.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance is_inv_l : IsInvL eq Z.zero Z.opp Z.add.
Proof. ecrush. Qed.

#[local] Instance is_inv_r : IsInvR eq Z.zero Z.opp Z.add.
Proof. ecrush. Qed.

#[local] Instance is_inv : IsInvLR eq Z.zero Z.opp Z.add.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance is_grp : IsGrp eq Z.zero Z.opp Z.add.
Proof. esplit; typeclasses eauto. Qed.

#[local] Instance is_comm : IsComm eq Z.add.
Proof. ecrush. Qed.

#[export] Hint Resolve has_bin_op has_null_op has_un_op is_assoc
  is_semigrp is_unl_l is_unl_r is_unl is_mon is_inv_l is_inv_r
  is_inv is_grp is_comm : typeclass_instances.

End Additive.

#[export] Hint Resolve has_equiv_rel : typeclass_instances.

(* Module Multiplicative.

Global Instance Z_bin_op_has_bin_op : HasBinOp Z := Z.mul.
Global Instance has_null_op : HasNullOp Z := Z.one.

Global Instance Z_bin_op_is_mag : IsMag eq (bin_op (A := Z)).
Proof. hnf. typeclasses eauto. Qed.

Global Instance Z_bin_op_is_assoc : IsAssoc (bin_op (A := Z)).
Proof. ecrush. Qed.

Global Instance Z_bin_op_is_semigrp : IsSemigrp (bin_op (A := Z)).
Proof. esplit; typeclasses eauto. Qed.

Global Instance Z_bin_op_is_comm : IsComm (bin_op (A := Z)).
Proof. ecrush. Qed.

Global Instance Z_bin_op_null_op_is_unl_l : IsUnlL null_op (bin_op (A := Z)).
Proof. ecrush. Qed.

Global Instance Z_bin_op_null_op_is_unl_r : IsUnlR null_op (bin_op (A := Z)).
Proof. ecrush. Qed.

Global Instance Z_bin_op_null_op_is_unl : IsUnlLR null_op (bin_op (A := Z)).
Proof. esplit; typeclasses eauto. Qed.

Global Instance Z_bin_op_null_op_is_mon : IsMon null_op (bin_op (A := Z)).
Proof. esplit; typeclasses eauto. Qed.

End Multiplicative.

Global Instance has_add : HasAdd Z := Z.add.
Global Instance has_zero : HasZero Z := Z.zero.
Global Instance has_neg : HasNeg Z := Z.opp.
Global Instance has_mul : HasMul Z := Z.mul.
Global Instance has_one : HasOne Z := Z.one.

Global Instance Z_add_is_comm : IsComm add.
Proof. ecrush. Qed.

Global Instance Z_add_mul_is_distr_l : IsDistrL mul add.
Proof. ecrush. Qed.

Global Instance Z_add_mul_is_distr_r : IsDistrR mul add.
Proof. ecrush. Qed.

Global Instance Z_add_mul_is_distr : IsDistrLR mul add.
Proof. esplit; typeclasses eauto. Qed.

Global Instance Z_zero_mul_is_absorb_elem_l : IsAbsorbElemL zero mul.
Proof. ecrush. Qed.

Global Instance Z_zero_mul_is_absorb_elem_r : IsAbsorbElemR zero mul.
Proof. ecrush. Qed.

Global Instance Z_zero_mul_is_absorb_elem_l_r : IsAbsorbElemLR zero mul.
Proof. esplit; typeclasses eauto. Qed.

Global Instance Z_zero_add_one_mul_is_semiring : IsSemiring zero add one mul.
Proof. esplit; typeclasses eauto. Qed.

Global Instance Z_zero_neg_add_one_mul_is_ring : IsRing zero neg add one mul.
Proof. esplit; typeclasses eauto. Qed.

Global Instance Z_mul_is_comm : IsComm mul.
Proof. ecrush. Qed.

(** TODO Organize the rest. *)

Global Instance has_equiv_rel : HasEquivRel Z := Z.eq.

Global Instance Z_equiv_is_refl : IsRefl Z.eq.
Proof. ecrush. Qed.

Global Instance Z_equiv_is_sym : IsSym Z.eq.
Proof. ecrush. Qed.

Global Instance Z_equiv_is_trans : IsTrans Z.eq.
Proof. ecrush. Qed.

Global Instance Z_equiv_is_part_equiv : IsPartEquiv Z.eq.
Proof. esplit; typeclasses eauto. Qed.

Global Instance Z_equiv_is_equiv : IsEquiv Z.eq.
Proof. esplit; typeclasses eauto. Qed.

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

Global Instance Z_N_is_iso_l_r : IsIsoLR Z_to_double_N Z_of_double_N.
Proof.
  split.
  - intros x. destruct x as [| p | p].
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
      * reflexivity. Qed. *)

(** TODO Organize this. *)

Section Context.

Import ZArith.ZArith.

Context (A : Type)
  {X : HasEquivRel A} {x : HasNullOp A} {f : HasUnOp A} {k : HasBinOp A}
  `{!IsGrp X x f k}.

(** ** Integer Repetition *)

Equations rep (n : Z) (y : A) : A :=
  rep Z0 y := 0;
  rep (Zpos n) y := Pos.iter_op _+_ n y;
  rep (Zneg n) y := - Pos.iter_op _+_ n y.

#[local] Instance Z_has_equiv_rel : HasEquivRel Z := Z.eq.
#[local] Instance Z_has_null_op : HasNullOp Z := Z.zero.
#[local] Instance Z_has_un_op : HasUnOp Z := Z.opp.
#[local] Instance Z_has_bin_op : HasBinOp Z := Z.add.

#[local] Instance Z_has_act_l : HasActL Z A := rep.

Context `{!IsGrp Z.eq Z.zero Z.opp Z.add}.

Ltac note := progress (
  (* try change Z.eq with (equiv_rel (A := Z)) in *;
  try change Z.zero with (null_op (A := Z)) in *;
  try change Z.opp with (un_op (A := Z)) in *;
  try change Z.add with (bin_op (A := Z)) in *; *)
  try change X with (equiv_rel (A := A)) in *;
  try change x with (null_op (A := A)) in *;
  try change f with (un_op (A := A)) in *;
  try change k with (bin_op (A := A)) in *).

(** Repetition by any integer a homomorphism. *)

Require Import Lia.

#[export] Instance rep_is_grp_hom (y : A) :
  IsGrpHom Z.eq Z.zero Z.opp Z.add X x f k (flip rep y).
Proof.
  note. split.
  - typeclasses eauto.
  - typeclasses eauto.
  - intros n p. unfold flip. destruct n as [| q | q].
    + unfold rep at 2. rewrite Z.add_0_l. rewrite unl_l. reflexivity.
    + unfold rep at 2. induction q as [| r a] using Pos.peano_ind.
      * unfold Pos.iter_op. rewrite Z.add_1_l. destruct (Z.succ p) eqn : a.
        assert (p = (- 1)%Z) by lia. subst p. cbn. rewrite inv_r. reflexivity.
        cbn. admit. admit.
      * admit.
    + admit.
  - typeclasses eauto. Admitted.

End Context.
