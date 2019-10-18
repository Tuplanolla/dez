From Coq Require Import
  ZArith.
From Maniunfold.Is Require Import
  TotalOrder NontrivialRing MonoidHomomorphism.

Module Equivalence.

Global Instance : HasEqv Z := Z.eq.

Global Instance : IsReflexive Z.eq := {}.
Proof. intros x. reflexivity. Qed.

Global Instance : IsSymmetric Z.eq := {}.
Proof. intros x y p. symmetry; auto. Qed.

Global Instance : IsTransitive Z.eq := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Global Instance : IsSetoid Z.eq := {}.

End Equivalence.

Module Order.

Global Instance : HasOrd Z := Z.le.

Global Instance : IsAntisymmetric Z.le := {}.
Proof. intros x y p q. apply Z.le_antisymm; auto. Qed.

Global Instance : IsTransitive Z.le := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Global Instance : IsConnex Z.le := {}.
Proof. intros x y. apply Z.le_ge_cases. Qed.

Global Instance : IsTotalOrder Z.le := {}.

End Order.

Module Additive.

Global Instance : HasOpr Z := Z.add.

Global Instance : IsAssociative Z.add := {}.
Proof. intros x y z. apply Z.add_assoc. Qed.

Global Instance : IsSemigroup Z.add := {}.

Global Instance : HasIdn Z := Z.zero.

Global Instance : IsLeftIdentifiable Z.add Z.zero := {}.
Proof. intros x. apply Z.add_0_l. Qed.

Global Instance : IsRightIdentifiable Z.add Z.zero := {}.
Proof. intros x. apply Z.add_0_r. Qed.

Global Instance : IsIdentifiable Z.add Z.zero := {}.

Global Instance : IsMonoid Z.add Z.zero := {}.

Global Instance : IsCommutative Z.add := {}.
Proof. intros x y. apply Z.add_comm. Qed.

Global Instance : IsCommutativeMonoid Z.add Z.zero := {}.

Global Instance : HasInv Z := Z.opp.

Global Instance : IsLeftInvertible Z.add Z.zero Z.opp := {}.
Proof. intros x. apply Z.add_opp_diag_l. Qed.

Global Instance : IsRightInvertible Z.add Z.zero Z.opp := {}.
Proof. intros x. apply Z.add_opp_diag_r. Qed.

Global Instance : IsInvertible Z.add Z.zero Z.opp := {}.

Global Instance : IsGroup Z.add Z.zero Z.opp := {}.

Global Instance : IsAbelianGroup Z.add Z.zero Z.opp := {}.

End Additive.

Module Multiplicative.

Global Instance : HasOpr Z := Z.mul.

Global Instance : IsAssociative Z.mul := {}.
Proof. intros x y z. apply Z.mul_assoc. Qed.

Global Instance : IsSemigroup Z.mul := {}.

Global Instance : HasIdn Z := Z.one.

Global Instance : IsLeftIdentifiable Z.mul Z.one := {}.
Proof. intros x. apply Z.mul_1_l. Qed.

Global Instance : IsRightIdentifiable Z.mul Z.one := {}.
Proof. intros x. apply Z.mul_1_r. Qed.

Global Instance : IsIdentifiable Z.mul Z.one := {}.

Global Instance : IsMonoid Z.mul Z.one := {}.

Global Instance : IsCommutative Z.mul := {}.
Proof. intros x y. apply Z.mul_comm. Qed.

Global Instance : IsCommutativeMonoid Z.mul Z.one := {}.

End Multiplicative.

Global Instance : HasAdd Z := Z.add.
Global Instance : HasMul Z := Z.mul.

Global Instance : HasZero Z := Z.zero.
Global Instance : HasOne Z := Z.one.

Global Instance : IsLeftDistributive Z.add Z.mul := {}.
Proof. intros x y z. apply Z.mul_add_distr_l. Qed.

Global Instance : IsRightDistributive Z.add Z.mul := {}.
Proof. intros x y z. apply Z.mul_add_distr_r. Qed.

Global Instance : IsDistributive Z.add Z.mul := {}.

Global Instance : IsSemiring Z.add Z.zero Z.mul Z.one := {}.

Global Instance : HasNeg Z := Z.opp.

Global Instance : IsRing Z.add Z.zero Z.opp Z.mul Z.one := {}.

Global Instance :
  IsNontrivialRing Z.add Z.zero Z.opp Z.mul Z.one := {}.
Proof. intros H. inversion H. Qed.
