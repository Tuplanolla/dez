(** * Properties of the Unit Type *)

From DEZ.Has Require Export
  EquivalenceRelations OrderRelations Decisions
  Operations ArithmeticOperations.
From DEZ.Is Require Export
  Truncated TotalOrder Group (* Field *) Ring.

(** TODO Move this. *)

(** ** Constant Constant Function *)

Equations const2 (A B C : Type) (x : A) (y : B) (z : C) : A :=
  const2 x _ _ := x.

Lemma const2_const_const (A B C : Type)
  (x : A) (y : B) (z : C) : const2 x y z = const (const x) y z.
Proof. reflexivity. Qed.

Ltac ecrush :=
  repeat (try typeclasses eauto; esplit);
  hnf in *; repeat match goal with
  | |- exists _ : unit, _ => exists tt
  | |- forall _ : unit, _ => intros ?
  | x : unit |- _ => destruct x
  end; eauto.

(** The unit type is contractive with respect to any reflexive relation. *)

#[export] Instance unit_is_contr (X : unit -> unit -> Prop)
  `{!IsRefl X} : IsContr X.
Proof. ecrush. Qed.

#[local] Existing Instance eq_is_contr_is_prop.

Equations unit_eq_dec (x y : unit) : {x = y} + {x <> y} :=
  unit_eq_dec x y := left (irrel x y).

Section Context.

#[local] Hint Unfold complement const2 : core.

#[local] Notation const2 := (@const2 _ unit unit).

(** ** Decidable Total Ordering *)

#[export] Instance unit_has_equiv_rel : HasEquivRel unit := _=_.
#[export] Instance unit_has_equiv_dec : HasEquivDec unit := unit_eq_dec.
#[export] Instance unit_has_ord_rel : HasOrdRel unit := const2 1.
#[export] Instance unit_has_str_ord_rel : HasOrdRel unit := const2 0.

#[export] Instance const2_1_is_refl : IsRefl (const2 1).
Proof. ecrush. Qed.

#[export] Instance const2_1_is_trans : IsTrans (const2 1).
Proof. ecrush. Qed.

#[export] Instance const2_1_is_connex : IsConnex (const2 1).
Proof. ecrush. Qed.

#[export] Instance const2_1_is_preord : IsPreord (const2 1).
Proof. ecrush. Qed.

#[export] Instance const2_1_is_antisym : IsAntisym _=_ (const2 1).
Proof. ecrush. Qed.

#[export] Instance const2_1_is_part_ord : IsPartOrd _=_ (const2 1).
Proof. ecrush. Qed.

#[export] Instance const2_1_is_tot_ord : IsTotOrd _=_ (const2 1).
Proof. ecrush. Qed.

#[export] Instance const2_0_is_trans : IsTrans (const2 0).
Proof. ecrush. Qed.

#[export] Instance const2_0_is_irrefl : IsIrrefl (const2 0).
Proof. ecrush. Qed.

#[export] Instance const2_0_is_str_connex : IsStrConnex _=_ (const2 0).
Proof. ecrush. Qed.

#[export] Instance const2_0_is_part_ord : IsStrPartOrd (const2 0).
Proof. ecrush. Qed.

#[export] Instance const2_0_is_str_tot_ord : IsStrTotOrd _=_ (const2 0).
Proof. ecrush. Qed.

(** ** Group *)

#[export] Instance unit_has_null_op : HasNullOp unit := tt.
#[export] Instance unit_has_un_op : HasUnOp unit := const tt.
#[export] Instance unit_has_bin_op : HasBinOp unit := const2 tt.

#[export] Instance unit_is_assoc : IsAssoc _=_ (const2 tt).
Proof. ecrush. Qed.

#[export] Instance unit_is_semigrp : IsSemigrp _=_ (const2 tt).
Proof. ecrush. Qed.

#[local] Instance unit_is_unl_elem_l : IsUnlElemL _=_ tt (const2 tt).
Proof. ecrush. Qed.

#[local] Instance unit_is_unl_elem_r : IsUnlElemR _=_ tt (const2 tt).
Proof. ecrush. Qed.

#[export] Instance unit_is_unl_elem : IsUnlElem _=_ tt (const2 tt).
Proof. ecrush. Qed.

#[export] Instance unit_is_mon : IsMon _=_ tt (const2 tt).
Proof. ecrush. Qed.

#[local] Instance unit_is_inv_l : IsInvL _=_ tt (const tt) (const2 tt).
Proof. ecrush. Qed.

#[local] Instance unit_is_inv_r : IsInvR _=_ tt (const tt) (const2 tt).
Proof. ecrush. Qed.

#[export] Instance unit_is_inv : IsInv _=_ tt (const tt) (const2 tt).
Proof. ecrush. Qed.

#[export] Instance unit_is_grp : IsGrp _=_ tt (const tt) (const2 tt).
Proof. ecrush. Qed.

#[export] Instance unit_is_comm_bin_op : IsCommBinOp _=_ (const2 tt).
Proof. ecrush. Qed.

(** ** Field *)

#[export] Instance unit_has_zero : HasZero unit := tt.
#[export] Instance unit_has_neg : HasNeg unit := const tt.
#[export] Instance unit_has_add : HasAdd unit := const2 tt.
#[export] Instance unit_has_one : HasOne unit := tt.
#[export] Instance unit_has_recip : HasRecip unit := const tt.
#[export] Instance unit_has_mul : HasMul unit := const2 tt.

#[local] Instance unit_is_distr_l : IsDistrL _=_ (const2 tt) (const2 tt).
Proof. ecrush. Qed.

#[local] Instance unit_is_distr_r : IsDistrR _=_ (const2 tt) (const2 tt).
Proof. ecrush. Qed.

#[export] Instance unit_is_distr : IsDistr _=_ (const2 tt) (const2 tt).
Proof. ecrush. Qed.

#[export] Instance unit_is_ring :
  IsRing _=_ tt (const tt) (const2 tt) tt (const2 tt).
Proof. ecrush. Qed.

End Context.
