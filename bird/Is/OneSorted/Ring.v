(* bad *)
From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation OneSorted.Multiplication
  OneSorted.One.
From Maniunfold.Is Require Export
  OneSorted.AbelianGroup OneSorted.Distributive OneSorted.Monoid
  OneSorted.Absorbing OneSorted.SignedAbsorbing OneSorted.BinaryCommutative
  OneSorted.BinaryCrossing OneSorted.BinarySplitCancellative
  OneSorted.Semiring OneSorted.Graded.Ring.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

(** Noncommutative ring. *)

Class IsRing (A : Type)
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A) : Prop := {
  A_add_zero_neg_is_ab_grp :> IsAbGrp A add zero neg;
  A_add_mul_is_distr :> IsDistr A add mul;
  A_mul_one_is_mon :> IsMon A mul one;
}.

Section Context.

Context {A : Type} `{is_ring : IsRing A}.

Ltac conversions := typeclasses
  convert bin_op into add and null_op into zero and un_op into neg or
  convert bin_op into mul and null_op into one.

Theorem A_zero_mul_l_absorb : forall x : A,
  0 * x = 0.
Proof with conversions.
  intros x.
  apply (l_cancel (0 * x) 0 (1 * x))...
  rewrite (r_unl (1 * x)).
  rewrite <- (r_distr 1 0 x).
  rewrite (r_unl 1).
  reflexivity. Defined.

Global Instance A_zero_mul_is_l_absorb : IsLAbsorb A zero mul.
Proof. intros x. apply A_zero_mul_l_absorb. Defined.

Theorem A_zero_mul_r_absorb : forall x : A,
  x * 0 = 0.
Proof with conversions.
  intros x.
  apply (l_cancel (x * 0) 0 (x * 1))...
  rewrite (r_unl (x * 1)).
  rewrite <- (l_distr x 1 0).
  rewrite (r_unl 1).
  reflexivity. Defined.

Global Instance A_zero_mul_is_r_absorb : IsRAbsorb A zero mul.
Proof. intros x. apply A_zero_mul_r_absorb. Defined.

Global Instance A_zero_mul_is_absorb : IsAbsorb A zero mul.
Proof. split; typeclasses eauto. Defined.

Theorem A_neg_mul_one_l_sgn_absorb : forall x : A,
  - (1) * x = - x.
Proof with conversions.
  intros x.
  apply (l_cancel (- (1) * x) (- x) x)...
  rewrite (r_inv x)...
  rewrite <- (l_unl x) at 1...
  rewrite <- (r_distr 1 (- (1)) x).
  rewrite (r_inv 1)...
  rewrite (l_absorb x).
  reflexivity. Defined.

Global Instance A_neg_mul_one_is_l_sgn_absorb : IsLSgnAbsorb A neg mul one.
Proof. intros x. apply A_neg_mul_one_l_sgn_absorb. Defined.

Theorem A_neg_mul_one_r_sgn_absorb : forall x : A,
  x * - (1) = - x.
Proof with conversions.
  intros x.
  apply (l_cancel (x * - (1)) (- x) x)...
  rewrite (r_inv x)...
  rewrite <- (r_unl x) at 1...
  rewrite <- (l_distr x).
  rewrite (r_inv 1)...
  rewrite (r_absorb x).
  reflexivity. Defined.

Global Instance A_neg_mul_one_is_r_sgn_absorb : IsRSgnAbsorb A neg mul one.
Proof. intros x. apply A_neg_mul_one_r_sgn_absorb. Defined.

Global Instance A_neg_mul_one_is_sgn_absorb : IsSgnAbsorb A neg mul one.
Proof. split; typeclasses eauto. Defined.

Theorem A_neg_mul_l_bin_comm : forall x y : A,
  - (x * y) = x * - y.
Proof with conversions.
  intros x y.
  rewrite <- (r_sgn_absorb (x * y)).
  rewrite <- (assoc x y (- (1)))...
  rewrite r_sgn_absorb.
  reflexivity. Defined.

Global Instance A_neg_mul_is_l_bin_comm : IsLBinComm A neg mul.
Proof. intros x y. apply A_neg_mul_l_bin_comm. Defined.

Theorem A_neg_mul_r_bin_comm : forall x y : A,
  - (x * y) = - x * y.
Proof with conversions.
  intros x y.
  rewrite <- (l_sgn_absorb (x * y)).
  rewrite (assoc (- (1)) x y)...
  rewrite l_sgn_absorb.
  reflexivity. Defined.

Global Instance A_neg_mul_is_r_bin_comm : IsRBinComm A neg mul.
Proof. intros x y. apply A_neg_mul_r_bin_comm. Defined.

Global Instance A_neg_mul_is_bin_comm : IsBinComm A neg mul.
Proof. split; typeclasses eauto. Defined.

Theorem A_neg_mul_bin_crs : forall x y : A,
  (- x) * y = x * (- y).
Proof with conversions.
  intros x y.
  rewrite <- (l_bin_comm x y).
  rewrite <- (r_bin_comm x y).
  reflexivity. Defined.

Global Instance A_neg_mul_is_bin_crs : IsBinCrs A neg mul.
Proof. intros x y. apply A_neg_mul_bin_crs. Defined.

Theorem A_neg_mul_bin_spt_cancel : forall x y : A,
  (- x) * (- y) = x * y.
Proof with conversions.
  intros x y.
  rewrite <- (r_bin_comm x (- y)).
  rewrite <- (l_bin_comm x y).
  rewrite (invol (x * y)).
  reflexivity. Defined.

Global Instance A_neg_mul_is_bin_spt_cancel : IsBinSptCancel A neg mul.
Proof. intros x y. apply A_neg_mul_bin_spt_cancel. Defined.

Global Instance A_add_zero_mul_one_is_sring : IsSring A add zero mul one.
Proof. split; typeclasses eauto. Defined.

(** TODO Clean up. *)

Local Instance unit_has_bin_op : HasBinOp unit := fun x y : unit => tt.

Local Instance bin_op_is_assoc : IsAssoc unit bin_op.
Proof. intros x y z. repeat match goal with t : unit |- _ => destruct t end.
  reflexivity. Defined.

Local Instance unit_has_null_op : HasNullOp unit := tt.

Local Instance bin_op_null_op_is_l_unl : IsLUnl unit bin_op null_op.
Proof. intros x. repeat match goal with t : unit |- _ => destruct t end.
  reflexivity. Defined.

Local Instance bin_op_null_op_is_r_unl : IsRUnl unit bin_op null_op.
Proof. intros x. repeat match goal with t : unit |- _ => destruct t end.
  reflexivity. Defined.

Local Instance const_A_has_add (i : unit) : HasAdd A := add.

Local Instance const_A_has_zero (i : unit) : HasZero A := zero.

Local Instance const_A_has_neg (i : unit) : HasNeg A := neg.

Local Instance const_A_has_grd_mul : HasGrdMul (A := unit) (const A) :=
  fun (i j : unit) (x y : A) => mul x y.

Local Instance const_A_has_grd_one : HasGrdOne (A := unit) (const A) :=
  one.

(** Every ring is a trivially graded ring. *)

Local Instance ring_is_grd_ring : IsGrdRing (A := unit) (const A)
  const_A_has_add const_A_has_zero const_A_has_neg
  const_A_has_grd_mul const_A_has_grd_one.
Proof. repeat split. all: try typeclasses eauto.
  all: cbv; intros.
  all: repeat match goal with t : unit |- _ => destruct t end.
  all: auto; try typeclasses eauto.
  - apply l_distr.
  - apply r_distr.
  - esplit. intros [] [] [] x y z. cbv. apply assoc.
  - esplit. intros [] x. cbv. apply l_unl.
  - esplit. intros [] x. cbv. apply r_unl. Defined.

End Context.
