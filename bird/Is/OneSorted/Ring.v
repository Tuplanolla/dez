From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Zero OneSorted.Negation OneSorted.Multiplication
  OneSorted.One.
From Maniunfold.Is Require Export
  OneSorted.AbelianGroup OneSorted.Distributive OneSorted.Monoid
  OneSorted.Absorbing OneSorted.SignedAbsorbing OneSorted.BinaryCommutative
  OneSorted.BinaryCrossing OneSorted.BinarySplitCancellative
  OneSorted.Semiring.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Class IsRing {A : Type}
  (A_has_add : HasAdd A) (has_zero : HasZero A) (has_neg : HasNeg A)
  (A_has_mul : HasMul A) (has_one : HasOne A) : Prop := {
  add_zero_neg_is_ab_grp :> IsAbGrp add zero neg;
  add_mul_is_distr :> IsDistr add mul;
  mul_one_is_mon :> IsMon mul one;
}.

Section Context.

Context {A : Type} `{is_ring : IsRing A}.

Ltac specializations := typeclasses specialize
  bin_op into add and null_op into zero and un_op into neg or
  bin_op into mul and null_op into one.

Theorem zero_mul_l_absorb : forall x : A,
  0 * x = 0.
Proof with specializations.
  intros x.
  apply (l_cancel (0 * x) 0 (1 * x))...
  rewrite (r_unl (1 * x)).
  rewrite <- (r_distr 1 0 x).
  rewrite (r_unl 1).
  reflexivity. Qed.

Global Instance zero_mul_is_l_absorb : IsLAbsorb zero mul.
Proof. intros x. apply zero_mul_l_absorb. Qed.

Theorem zero_mul_r_absorb : forall x : A,
  x * 0 = 0.
Proof with specializations.
  intros x.
  apply (l_cancel (x * 0) 0 (x * 1))...
  rewrite (r_unl (x * 1)).
  rewrite <- (l_distr x 1 0).
  rewrite (r_unl 1).
  reflexivity. Qed.

Global Instance zero_mul_is_r_absorb : IsRAbsorb zero mul.
Proof. intros x. apply zero_mul_r_absorb. Qed.

Global Instance zero_mul_is_absorb : IsAbsorb zero mul.
Proof. constructor; typeclasses eauto. Qed.

Theorem neg_mul_one_l_sgn_absorb : forall x : A,
  - (1) * x = - x.
Proof with specializations.
  intros x.
  apply (l_cancel (- (1) * x) (- x) x)...
  rewrite (r_inv x)...
  rewrite <- (l_unl x) at 1...
  rewrite <- (r_distr 1 (- (1)) x).
  rewrite (r_inv 1)...
  rewrite (l_absorb x).
  reflexivity. Qed.

Global Instance neg_mul_one_is_l_sgn_absorb : IsLSgnAbsorb neg mul one.
Proof. intros x. apply neg_mul_one_l_sgn_absorb. Qed.

Theorem neg_mul_one_r_sgn_absorb : forall x : A,
  x * - (1) = - x.
Proof with specializations.
  intros x.
  apply (l_cancel (x * - (1)) (- x) x)...
  rewrite (r_inv x)...
  rewrite <- (r_unl x) at 1...
  rewrite <- (l_distr x).
  rewrite (r_inv 1)...
  rewrite (r_absorb x).
  reflexivity. Qed.

Global Instance neg_mul_one_is_r_sgn_absorb : IsRSgnAbsorb neg mul one.
Proof. intros x. apply neg_mul_one_r_sgn_absorb. Qed.

Global Instance neg_mul_one_is_sgn_absorb : IsSgnAbsorb neg mul one.
Proof. constructor; typeclasses eauto. Qed.

Theorem neg_mul_l_bin_comm : forall x y : A,
  - (x * y) = - x * y.
Proof with specializations.
  intros x y.
  rewrite <- (l_sgn_absorb (x * y)).
  rewrite (assoc (- (1)) x y)...
  rewrite l_sgn_absorb.
  reflexivity. Qed.

Global Instance neg_mul_is_l_bin_comm : IsLBinComm neg mul.
Proof. intros x y. apply neg_mul_l_bin_comm. Qed.

Theorem neg_mul_r_bin_comm : forall x y : A,
  - (x * y) = x * - y.
Proof with specializations.
  intros x y.
  rewrite <- (r_sgn_absorb (x * y)).
  rewrite <- (assoc x y (- (1)))...
  rewrite r_sgn_absorb.
  reflexivity. Qed.

Global Instance neg_mul_is_r_bin_comm : IsRBinComm neg mul.
Proof. intros x y. apply neg_mul_r_bin_comm. Qed.

Global Instance neg_mul_is_bin_comm : IsBinComm neg mul.
Proof. constructor; typeclasses eauto. Qed.

Theorem neg_mul_bin_crs : forall x y : A,
  (- x) * y = x * (- y).
Proof with specializations.
  intros x y.
  rewrite <- (l_bin_comm x y).
  rewrite <- (r_bin_comm x y).
  reflexivity. Qed.

Global Instance neg_mul_is_bin_crs : IsBinCrs neg mul.
Proof. intros x y. apply neg_mul_bin_crs. Qed.

Theorem neg_mul_bin_spt_cancel : forall x y : A,
  (- x) * (- y) = x * y.
Proof with specializations.
  intros x y.
  rewrite <- (l_bin_comm x (- y)).
  rewrite <- (r_bin_comm x y).
  rewrite (invol (x * y)).
  reflexivity. Qed.

Global Instance neg_mul_is_bin_spt_cancel : IsBinSptCancel neg mul.
Proof. intros x y. apply neg_mul_bin_spt_cancel. Qed.

Global Instance add_zero_mul_one_is_sring : IsSring add zero mul one.
Proof. constructor; typeclasses eauto. Qed.

End Context.
