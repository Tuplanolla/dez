From Coq Require Import
  NArith.
From Maniunfold.Is Require Import
  TotalOrder Semiring MonoidHomomorphism.

Module Equivalence.

Instance N_has_eqv : HasEqv N := fun x y : N => x = y.

Instance N_is_reflexive : IsReflexive N := {}.
Proof. intros x. reflexivity. Qed.

Instance N_is_symmetric : IsSymmetric N := {}.
Proof. intros x y p. symmetry; auto. Qed.

Instance N_is_transitive : IsTransitive N := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Instance N_is_setoid : IsSetoid N := {}.

End Equivalence.

Module Order.

Instance N_has_ord : HasOrd N := fun x y : N => (x <= y)%N.

Instance N_is_antisymmetric : IsAntisymmetric N := {}.
Proof. intros x y p q. apply N.le_antisymm; auto. Qed.

Instance N_is_transitive : IsTransitive N := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Instance N_is_connex : IsConnex N := {}.
Proof. intros x y. apply N.le_ge_cases. Qed.

Instance N_is_total_order : IsTotalOrder N := {}.

End Order.

Module Additive.

Instance N_has_opr : HasOpr N := fun x y : N => (x + y)%N.

Instance N_is_associative : IsAssociative N := {}.
Proof. intros x y z. apply N.add_assoc. Qed.

Instance N_is_semigroup : IsSemigroup N := {}.

Instance N_has_idn : HasIdn N := 0%N.

Instance N_is_left_identifiable : IsLeftIdentifiable N := {}.
Proof. intros x. apply N.add_0_l. Qed.

Instance N_is_right_identifiable : IsRightIdentifiable N := {}.
Proof. intros x. apply N.add_0_r. Qed.

Instance N_is_identifiable : IsIdentifiable N := {}.

Instance N_is_monoid : IsMonoid N := {}.

Instance N_is_commutative : IsCommutative N := {}.
Proof. intros x y. apply N.add_comm. Qed.

Instance N_is_commutative_monoid : IsCommutativeMonoid N := {}.

End Additive.

Module Multiplicative.

Instance N_has_opr : HasOpr N := fun x y : N => (x * y)%N.

Instance N_is_associative : IsAssociative N := {}.
Proof. intros x y z. apply N.mul_assoc. Qed.

Instance N_is_semigroup : IsSemigroup N := {}.

Instance N_has_idn : HasIdn N := 1%N.

Instance N_is_left_identifiable : IsLeftIdentifiable N := {}.
Proof. intros x. apply N.mul_1_l. Qed.

Instance N_is_right_identifiable : IsRightIdentifiable N := {}.
Proof. intros x. apply N.mul_1_r. Qed.

Instance N_is_identifiable : IsIdentifiable N := {}.

Instance N_is_monoid : IsMonoid N := {}.

Instance N_is_commutative : IsCommutative N := {}.
Proof. intros x y. apply N.mul_comm. Qed.

Instance N_is_commutative_monoid : IsCommutativeMonoid N := {}.

End Multiplicative.

Instance N_has_add : HasAdd N := opr (HasOpr := Additive.N_has_opr).
Instance N_has_mul : HasMul N := opr (HasOpr := Multiplicative.N_has_opr).

Instance N_has_zero : HasZero N := idn (HasIdn := Additive.N_has_idn).
Instance N_has_one : HasOne N := idn (HasIdn := Multiplicative.N_has_idn).

Instance N_is_left_distributive : IsLeftDistributive N := {}.
Proof. intros x y z. apply N.mul_add_distr_l. Qed.

Instance N_is_right_distributive : IsRightDistributive N := {}.
Proof. intros x y z. apply N.mul_add_distr_r. Qed.

Instance N_is_distributive : IsDistributive N := {}.

Instance N_is_semiring : IsSemiring N := {}.

Instance N_has_hom : HasHom N N := fun x : N => (2 ^ x)%N.

Instance N_is_setoid_homomorphism : IsSetoidHomomorphism N N := {}.

Instance N_is_semigroup_homomorphism : IsSemigroupHomomorphism N N
  (A_has_opr := add) (B_has_opr := mul) := {}.
Proof.
  intros x y. cbv -[N.add N.mul N.pow]. rewrite N.pow_add_r. reflexivity. Qed.

Instance N_is_monoid_homomorphism : IsMonoidHomomorphism N N
  (A_has_opr := add) (A_has_idn := zero)
  (B_has_opr := mul) (B_has_idn := one) := {}.
Proof. reflexivity. Qed.
