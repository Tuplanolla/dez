(* bad *)
From Coq Require Import
  Logic.Eqdep_dec.
From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation OneSorted.Multiplication
  OneSorted.One.
From Maniunfold.Is Require Export
  OneSorted.AbelianGroup OneSorted.Distributive OneSorted.Monoid
  OneSorted.Absorbing OneSorted.SignedAbsorbing OneSorted.BinaryCommutative
  OneSorted.BinaryCrossing OneSorted.BinarySplitCancellative
  OneSorted.Degenerate OneSorted.Semiring OneSorted.Graded.Ring.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.
From Maniunfold.ShouldHave Require
  OneSorted.Graded.AdditiveNotations OneSorted.Graded.ArithmeticNotations.

(** Ring, abelian group distributing over a monoid. *)

Class IsRing (A : Type)
  `(HasAdd A) `(HasZero A) `(HasNeg A) `(HasMul A) `(HasOne A) : Prop := {
  add_zero_neg_is_ab_grp :> IsAbGrp add zero neg;
  add_mul_is_distr :> IsDistr add mul;
  mul_one_is_mon :> IsMon mul one;
}.

Section Context.

Context (A : Type) `(IsRing A).

Ltac conversions := typeclasses
  convert bin_op into add and null_op into zero and un_op into neg or
  convert bin_op into mul and null_op into one.

Theorem zero_mul_l_absorb (x : A) : 0 * x = 0.
Proof with conversions.
  apply (l_cancel (0 * x) 0 (1 * x))...
  rewrite (r_unl (1 * x)).
  rewrite <- (r_distr 1 0 x).
  rewrite (r_unl 1).
  reflexivity. Qed.

Global Instance zero_mul_is_l_absorb : IsLAbsorb zero mul.
Proof. exact @zero_mul_l_absorb. Qed.

Theorem zero_mul_r_absorb (x : A) : x * 0 = 0.
Proof with conversions.
  apply (l_cancel (x * 0) 0 (x * 1))...
  rewrite (r_unl (x * 1)).
  rewrite <- (l_distr x 1 0).
  rewrite (r_unl 1).
  reflexivity. Qed.

Global Instance zero_mul_is_r_absorb : IsRAbsorb zero mul.
Proof. exact @zero_mul_r_absorb. Qed.

Global Instance zero_mul_is_absorb : IsAbsorb zero mul.
Proof. split; typeclasses eauto. Qed.

Theorem zero_neg_un_absorb : - 0 = 0.
Proof with conversions.
  apply (l_cancel (- 0) 0 0)...
  rewrite (r_inv 0)...
  rewrite (r_unl 0).
  reflexivity. Qed.

Global Instance zero_neg_is_un_absorb : IsUnAbsorb zero neg.
Proof. exact @zero_neg_un_absorb. Qed.

Theorem neg_mul_one_l_sgn_absorb (x : A) : (- 1) * x = - x.
Proof with conversions.
  apply (l_cancel ((- 1) * x) (- x) (1 * x))...
  rewrite <- (r_distr 1 (- 1) x).
  rewrite (r_inv 1)...
  rewrite (l_absorb x).
  rewrite (l_unl x).
  rewrite (r_inv x)...
  reflexivity. Qed.

Global Instance neg_mul_one_is_l_sgn_absorb : IsLSgnAbsorb neg mul one.
Proof. exact @neg_mul_one_l_sgn_absorb. Qed.

Theorem neg_mul_one_r_sgn_absorb (x : A) : x * (- 1) = - x.
Proof with conversions.
  apply (l_cancel (x * (- 1)) (- x) (x * 1))...
  rewrite <- (l_distr x 1 (- 1)).
  rewrite (r_inv 1)...
  rewrite (r_absorb x).
  rewrite (r_unl x).
  rewrite (r_inv x)...
  reflexivity. Qed.

Global Instance neg_mul_one_is_r_sgn_absorb : IsRSgnAbsorb neg mul one.
Proof. exact @neg_mul_one_r_sgn_absorb. Qed.

Global Instance neg_mul_one_is_sgn_absorb : IsSgnAbsorb neg mul one.
Proof. split; typeclasses eauto. Qed.

Theorem neg_mul_l_bin_comm (x y : A) : - (x * y) = x * (- y).
Proof with conversions.
  rewrite <- (r_sgn_absorb (x * y)).
  rewrite <- (assoc x y (- 1))...
  rewrite r_sgn_absorb.
  reflexivity. Qed.

Global Instance neg_mul_is_l_bin_comm : IsLBinComm neg mul.
Proof. exact @neg_mul_l_bin_comm. Qed.

Theorem neg_mul_r_bin_comm (x y : A) : - (x * y) = (- x) * y.
Proof with conversions.
  rewrite <- (l_sgn_absorb (x * y)).
  rewrite (assoc (- 1) x y)...
  rewrite l_sgn_absorb.
  reflexivity. Qed.

Global Instance neg_mul_is_r_bin_comm : IsRBinComm neg mul.
Proof. exact @neg_mul_r_bin_comm. Qed.

Global Instance neg_mul_is_bin_comm : IsBinComm neg mul.
Proof. split; typeclasses eauto. Qed.

Theorem neg_mul_bin_crs (x y : A) : (- x) * y = x * (- y).
Proof with conversions.
  rewrite <- (l_bin_comm x y).
  rewrite <- (r_bin_comm x y).
  reflexivity. Qed.

Global Instance neg_mul_is_bin_crs : IsBinCrs neg mul.
Proof. exact @neg_mul_bin_crs. Qed.

Theorem neg_mul_bin_spt_cancel (x y : A) : (- x) * (- y) = x * y.
Proof with conversions.
  rewrite <- (r_bin_comm x (- y)).
  rewrite <- (l_bin_comm x y).
  rewrite (invol (x * y)).
  reflexivity. Qed.

Global Instance neg_mul_is_bin_spt_cancel : IsBinSptCancel neg mul.
Proof. exact @neg_mul_bin_spt_cancel. Qed.

Global Instance add_zero_mul_one_is_sring : IsSring add zero mul one.
Proof. split; typeclasses eauto. Qed.

Theorem one_zero_degen (x : A) (e : 1 = 0) : x = 0.
Proof with conversions.
  pose proof l_distr x 0 1 as e'.
  rewrite l_unl in e'. rewrite r_unl in e' at 1. rewrite e in e'.
  repeat rewrite r_absorb in e'. rewrite r_unl in e'. apply e'. Qed.

Global Instance one_zero_is_degen : IsDegen zero one.
Proof. exact @one_zero_degen. Qed.

(** TODO Clean up. *)

Import OneSorted.Graded.ArithmeticNotations.
Import OneSorted.Graded.AdditiveNotations.

Local Instance unit_has_bin_op : HasBinOp unit := fun x y : unit => tt.

Local Instance bin_op_is_assoc : IsAssoc (bin_op (A := unit)).
Proof. intros x y z. repeat match goal with t : unit |- _ => destruct t end.
  reflexivity. Qed.

Local Instance unit_has_null_op : HasNullOp unit := tt.

Local Instance bin_op_null_op_is_l_unl : IsLUnl bin_op null_op.
Proof. intros x. repeat match goal with t : unit |- _ => destruct t end.
  reflexivity. Qed.

Local Instance bin_op_null_op_is_r_unl : IsRUnl bin_op null_op.
Proof. intros x. repeat match goal with t : unit |- _ => destruct t end.
  reflexivity. Qed.

Local Instance const_has_add (i : unit) : HasAdd A := add.

Local Instance const_has_zero (i : unit) : HasZero A := zero.

Local Instance const_has_neg (i : unit) : HasNeg A := neg.

Local Instance const_has_grd_mul : HasGrdMul (A := unit) (const A) :=
  fun (i j : unit) (x y : A) => mul x y.

Local Instance const_has_grd_one : HasGrdOne (A := unit) (const A) :=
  one.

(** Every ring is a trivially graded ring. *)

Local Instance ring_is_grd_ring : IsGrdRing (A := unit) (const A)
  const_has_add const_has_zero const_has_neg
  const_has_grd_mul const_has_grd_one.
Proof. repeat split. all: try typeclasses eauto.
  all: hnf; intros.
  all: repeat match goal with t : unit |- _ => destruct t end.
  all: auto; try typeclasses eauto.
  - apply l_distr.
  - apply r_distr.
  - esplit. intros [] [] [] x y z.
    rewrite <- eq_rect_eq_dec; try decide equality.
    apply assoc.
  - esplit. intros [] x.
    rewrite <- eq_rect_eq_dec; try decide equality.
    apply l_unl.
  - esplit. intros [] x.
    rewrite <- eq_rect_eq_dec; try decide equality.
    apply r_unl. Qed.

End Context.
