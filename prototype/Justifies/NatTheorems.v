From Coq Require Import
  PeanoNat.
From Maniunfold.Is Require Import
  TotalOrder Semiring MonoidHomomorphism.

Module Equivalence.

Instance nat_has_eqv : HasEqv nat := Nat.eq.

Instance nat_is_reflexive : IsReflexive Nat.eq := {}.
Proof. intros x. reflexivity. Qed.

Instance nat_is_symmetric : IsSymmetric Nat.eq := {}.
Proof. intros x y p. symmetry; auto. Qed.

Instance nat_is_transitive : IsTransitive Nat.eq := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Instance nat_is_setoid : IsSetoid Nat.eq := {}.

End Equivalence.

Module Order.

Instance nat_has_ord : HasOrd nat := Nat.le.

Instance nat_is_antisymmetric : IsAntisymmetric Nat.le := {}.
Proof. intros x y p q. apply Nat.le_antisymm; auto. Qed.

Instance nat_is_transitive : IsTransitive Nat.le := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Instance nat_is_connex : IsConnex Nat.le := {}.
Proof. intros x y. apply Nat.le_ge_cases. Qed.

Instance nat_is_total_order : IsTotalOrder Nat.le := {}.
Proof. cbv -[Nat.le]. apply Nat.le_wd. Qed.

End Order.

Module Additive.

Instance nat_has_opr : HasOpr nat := Nat.add.

Instance nat_is_associative : IsAssociative Nat.add := {}.
Proof. intros x y z. apply Nat.add_assoc. Qed.

Instance nat_is_semigroup : IsSemigroup Nat.add := {}.
Proof. cbv -[Nat.add]. apply Nat.add_wd. Qed.

Instance nat_has_idn : HasIdn nat := Nat.zero.

Instance nat_is_left_identifiable : IsLeftIdentifiable Nat.add Nat.zero := {}.
Proof. intros x. apply Nat.add_0_l. Qed.

Instance nat_is_right_identifiable :
  IsRightIdentifiable Nat.add Nat.zero := {}.
Proof. intros x. apply Nat.add_0_r. Qed.

Instance nat_is_identifiable : IsIdentifiable Nat.add Nat.zero := {}.

Instance nat_is_monoid : IsMonoid Nat.add Nat.zero := {}.

Instance nat_is_commutative : IsCommutative Nat.add := {}.
Proof. intros x y. apply Nat.add_comm. Qed.

Instance nat_is_commutative_monoid :
  IsCommutativeMonoid Nat.add Nat.zero := {}.

End Additive.

Module Multiplicative.

Instance nat_has_opr : HasOpr nat := Nat.mul.

Instance nat_is_associative : IsAssociative Nat.mul := {}.
Proof. intros x y z. apply Nat.mul_assoc. Qed.

Instance nat_is_semigroup : IsSemigroup Nat.mul := {}.
Proof. cbv -[Nat.mul]. apply Nat.mul_wd. Qed.

Instance nat_has_idn : HasIdn nat := Nat.one.

Instance nat_is_left_identifiable : IsLeftIdentifiable Nat.mul Nat.one := {}.
Proof. intros x. apply Nat.mul_1_l. Qed.

Instance nat_is_right_identifiable : IsRightIdentifiable Nat.mul Nat.one := {}.
Proof. intros x. apply Nat.mul_1_r. Qed.

Instance nat_is_identifiable : IsIdentifiable Nat.mul Nat.one := {}.

Instance nat_is_monoid : IsMonoid Nat.mul Nat.one := {}.

Instance nat_is_commutative : IsCommutative Nat.mul := {}.
Proof. intros x y. apply Nat.mul_comm. Qed.

Instance nat_is_commutative_monoid : IsCommutativeMonoid Nat.mul Nat.one := {}.

End Multiplicative.

Instance nat_has_add : HasAdd nat := Nat.add.
Instance nat_has_mul : HasMul nat := Nat.mul.

Instance nat_has_zero : HasZero nat := Nat.zero.
Instance nat_has_one : HasOne nat := Nat.one.

Instance nat_is_left_distributive : IsLeftDistributive Nat.add Nat.mul := {}.
Proof. intros x y z. apply Nat.mul_add_distr_l. Qed.

Instance nat_is_right_distributive : IsRightDistributive Nat.add Nat.mul := {}.
Proof. intros x y z. apply Nat.mul_add_distr_r. Qed.

Instance nat_is_distributive : IsDistributive Nat.add Nat.mul := {}.

Instance nat_is_semiring : IsSemiring Nat.add Nat.zero Nat.mul Nat.one := {}.

Definition nat_pow2 (x : nat) : nat := 2 ^ x.

Instance nat_has_hom : HasHom nat nat := nat_pow2.

Instance nat_is_setoid_homomorphism : IsSetoidHomomorphism nat_pow2 := {}.
Proof. cbv -[Nat.pow]. apply Nat.pow_wd. reflexivity. Qed.

Instance nat_is_semigroup_homomorphism :
  IsSemigroupHomomorphism Nat.add Nat.mul nat_pow2 := {}.
Proof. intros x y. apply Nat.pow_add_r. Qed.

Instance nat_is_monoid_homomorphism :
  IsMonoidHomomorphism Nat.add Nat.zero Nat.mul Nat.one nat_pow2 := {}.
Proof. reflexivity. Qed.
