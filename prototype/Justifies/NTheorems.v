From Coq Require Import
  NArith.
From Maniunfold.Is Require Import
  TotalOrder Semiring MonoidHomomorphism.

Module Equivalence.

Global Instance : HasEqv N := N.eq.

Global Instance : IsReflexive N.eq := {}.
Proof. intros x. reflexivity. Qed.

Global Instance : IsSymmetric N.eq := {}.
Proof. intros x y p. symmetry; auto. Qed.

Global Instance : IsTransitive N.eq := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Global Instance : IsSetoid N.eq := {}.

End Equivalence.

Module Order.

Global Instance : HasOrd N := N.le.

Global Instance : IsAntisymmetric N.le := {}.
Proof. intros x y p q. apply N.le_antisymm; auto. Qed.

Global Instance : IsTransitive N.le := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Global Instance : IsConnex N.le := {}.
Proof. intros x y. apply N.le_ge_cases. Qed.

Global Instance : IsTotalOrder N.le := {}.

End Order.

Module Additive.

Global Instance : HasOpr N := N.add.

Global Instance : IsAssociative N.add := {}.
Proof. intros x y z. apply N.add_assoc. Qed.

Global Instance : IsSemigroup N.add := {}.

Global Instance : HasIdn N := N.zero.

Global Instance : IsLeftIdentifiable N.add N.zero := {}.
Proof. intros x. apply N.add_0_l. Qed.

Global Instance : IsRightIdentifiable N.add N.zero := {}.
Proof. intros x. apply N.add_0_r. Qed.

Global Instance : IsIdentifiable N.add N.zero := {}.

Global Instance : IsMonoid N.add N.zero := {}.

Global Instance : IsCommutative N.add := {}.
Proof. intros x y. apply N.add_comm. Qed.

Global Instance : IsCommutativeMonoid N.add N.zero := {}.

End Additive.

Module Multiplicative.

Global Instance : HasOpr N := N.mul.

Global Instance : IsAssociative N.mul := {}.
Proof. intros x y z. apply N.mul_assoc. Qed.

Global Instance : IsSemigroup N.mul := {}.

Global Instance : HasIdn N := N.one.

Global Instance : IsLeftIdentifiable N.mul N.one := {}.
Proof. intros x. apply N.mul_1_l. Qed.

Global Instance : IsRightIdentifiable N.mul N.one := {}.
Proof. intros x. apply N.mul_1_r. Qed.

Global Instance : IsIdentifiable N.mul N.one := {}.

Global Instance : IsMonoid N.mul N.one := {}.

Global Instance : IsCommutative N.mul := {}.
Proof. intros x y. apply N.mul_comm. Qed.

Global Instance : IsCommutativeMonoid N.mul N.one := {}.

End Multiplicative.

Global Instance : HasAdd N := N.add.
Global Instance : HasMul N := N.mul.

Global Instance : HasZero N := N.zero.
Global Instance : HasOne N := N.one.

Global Instance : IsLeftDistributive N.add N.mul := {}.
Proof. intros x y z. apply N.mul_add_distr_l. Qed.

Global Instance : IsRightDistributive N.add N.mul := {}.
Proof. intros x y z. apply N.mul_add_distr_r. Qed.

Global Instance : IsDistributive N.add N.mul := {}.

Global Instance : IsSemiring N.add N.zero N.mul N.one := {}.

Definition N_pow2 (x : N) : N := (2 ^ x)%N.

Global Instance : HasHom N N := N_pow2.

Global Instance : IsSetoidHomomorphism N_pow2 := {}.

Global Instance :
  IsSemigroupHomomorphism N.add N.mul N_pow2 := {}.
Proof. intros x y. apply N.pow_add_r. Qed.

Global Instance :
  IsMonoidHomomorphism N.add N.zero N.mul N.one N_pow2 := {}.
Proof. reflexivity. Qed.
