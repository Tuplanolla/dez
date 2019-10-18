From Coq Require Import
  PeanoNat.
From Maniunfold.Is Require Import
  TotalOrder Semiring MonoidHomomorphism.

Module Equivalence.

Global Instance : HasEqv nat := Nat.eq.

Global Instance : IsReflexive Nat.eq := {}.
Proof. intros x. reflexivity. Qed.

Global Instance : IsSymmetric Nat.eq := {}.
Proof. intros x y p. symmetry; auto. Qed.

Global Instance : IsTransitive Nat.eq := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Global Instance : IsSetoid Nat.eq := {}.

End Equivalence.

Module Order.

Global Instance : HasOrd nat := Nat.le.

Global Instance : IsAntisymmetric Nat.le := {}.
Proof. intros x y p q. apply Nat.le_antisymm; auto. Qed.

Global Instance : IsTransitive Nat.le := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Global Instance : IsConnex Nat.le := {}.
Proof. intros x y. apply Nat.le_ge_cases. Qed.

Global Instance : IsTotalOrder Nat.le := {}.

End Order.

Module Additive.

Global Instance : HasOpr nat := Nat.add.

Global Instance : IsAssociative Nat.add := {}.
Proof. intros x y z. apply Nat.add_assoc. Qed.

Global Instance : IsSemigroup Nat.add := {}.

Global Instance : HasIdn nat := Nat.zero.

Global Instance : IsLeftIdentifiable Nat.add Nat.zero := {}.
Proof. intros x. apply Nat.add_0_l. Qed.

Global Instance :
  IsRightIdentifiable Nat.add Nat.zero := {}.
Proof. intros x. apply Nat.add_0_r. Qed.

Global Instance : IsIdentifiable Nat.add Nat.zero := {}.

Global Instance : IsMonoid Nat.add Nat.zero := {}.

Global Instance : IsCommutative Nat.add := {}.
Proof. intros x y. apply Nat.add_comm. Qed.

Global Instance :
  IsCommutativeMonoid Nat.add Nat.zero := {}.

End Additive.

Module Multiplicative.

Global Instance : HasOpr nat := Nat.mul.

Global Instance : IsAssociative Nat.mul := {}.
Proof. intros x y z. apply Nat.mul_assoc. Qed.

Global Instance : IsSemigroup Nat.mul := {}.

Global Instance : HasIdn nat := Nat.one.

Global Instance : IsLeftIdentifiable Nat.mul Nat.one := {}.
Proof. intros x. apply Nat.mul_1_l. Qed.

Global Instance : IsRightIdentifiable Nat.mul Nat.one := {}.
Proof. intros x. apply Nat.mul_1_r. Qed.

Global Instance : IsIdentifiable Nat.mul Nat.one := {}.

Global Instance : IsMonoid Nat.mul Nat.one := {}.

Global Instance : IsCommutative Nat.mul := {}.
Proof. intros x y. apply Nat.mul_comm. Qed.

Global Instance : IsCommutativeMonoid Nat.mul Nat.one := {}.

End Multiplicative.

Global Instance : HasAdd nat := Nat.add.
Global Instance : HasMul nat := Nat.mul.

Global Instance : HasZero nat := Nat.zero.
Global Instance : HasOne nat := Nat.one.

Global Instance : IsLeftDistributive Nat.add Nat.mul := {}.
Proof. intros x y z. apply Nat.mul_add_distr_l. Qed.

Global Instance : IsRightDistributive Nat.add Nat.mul := {}.
Proof. intros x y z. apply Nat.mul_add_distr_r. Qed.

Global Instance : IsDistributive Nat.add Nat.mul := {}.

Global Instance : IsSemiring Nat.add Nat.zero Nat.mul Nat.one := {}.

Definition nat_pow2 (x : nat) : nat := 2 ^ x.

Global Instance : HasHom nat nat := nat_pow2.

Global Instance : IsSetoidHomomorphism nat_pow2 := {}.

Global Instance :
  IsSemigroupHomomorphism Nat.add Nat.mul nat_pow2 := {}.
Proof. intros x y. apply Nat.pow_add_r. Qed.

Global Instance :
  IsMonoidHomomorphism Nat.add Nat.zero Nat.mul Nat.one nat_pow2 := {}.
Proof. reflexivity. Qed.
