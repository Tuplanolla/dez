From Coq Require Import
  NArith.
From Maniunfold.Is Require Import
  TotalOrder Semiring MonoidHomomorphism.

Module Equivalence.

Definition N_eqv (x y : N) : Prop := x = y.

Instance N_has_eqv : HasEqv N := N_eqv.

Instance N_is_reflexive : IsReflexive N_eqv := {}.
Proof. intros x. reflexivity. Qed.

Instance N_is_symmetric : IsSymmetric N_eqv := {}.
Proof. intros x y p. symmetry; auto. Qed.

Instance N_is_transitive : IsTransitive N_eqv := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Instance N_is_setoid : IsSetoid N_eqv := {}.

End Equivalence.

Module Order.

Instance N_has_ord : HasOrd N := N.le.

Instance N_is_antisymmetric : IsAntisymmetric N.le := {}.
Proof. intros x y p q. apply N.le_antisymm; auto. Qed.

Instance N_is_transitive : IsTransitive N.le := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Instance N_is_connex : IsConnex N.le := {}.
Proof. intros x y. apply N.le_ge_cases. Qed.

Instance N_is_total_order : IsTotalOrder N.le := {}.

End Order.

Module Additive.

Instance N_has_opr : HasOpr N := N.add.

Instance N_is_associative : IsAssociative N.add := {}.
Proof. intros x y z. apply N.add_assoc. Qed.

Instance N_is_semigroup : IsSemigroup N.add := {}.

Instance N_has_idn : HasIdn N := N.zero.

Instance N_is_left_identifiable : IsLeftIdentifiable N.add N.zero := {}.
Proof. intros x. apply N.add_0_l. Qed.

Instance N_is_right_identifiable : IsRightIdentifiable N.add N.zero := {}.
Proof. intros x. apply N.add_0_r. Qed.

Instance N_is_identifiable : IsIdentifiable N.add N.zero := {}.

Instance N_is_monoid : IsMonoid N.add N.zero := {}.

Instance N_is_commutative : IsCommutative N.add := {}.
Proof. intros x y. apply N.add_comm. Qed.

Instance N_is_commutative_monoid : IsCommutativeMonoid N.add N.zero := {}.

End Additive.

Module Multiplicative.

Instance N_has_opr : HasOpr N := N.mul.

Instance N_is_associative : IsAssociative N.mul := {}.
Proof. intros x y z. apply N.mul_assoc. Qed.

Instance N_is_semigroup : IsSemigroup N.mul := {}.

Instance N_has_idn : HasIdn N := N.one.

Instance N_is_left_identifiable : IsLeftIdentifiable N.mul N.one := {}.
Proof. intros x. apply N.mul_1_l. Qed.

Instance N_is_right_identifiable : IsRightIdentifiable N.mul N.one := {}.
Proof. intros x. apply N.mul_1_r. Qed.

Instance N_is_identifiable : IsIdentifiable N.mul N.one := {}.

Instance N_is_monoid : IsMonoid N.mul N.one := {}.

Instance N_is_commutative : IsCommutative N.mul := {}.
Proof. intros x y. apply N.mul_comm. Qed.

Instance N_is_commutative_monoid : IsCommutativeMonoid N.mul N.one := {}.

End Multiplicative.

Instance N_has_add : HasAdd N := opr (HasOpr := Additive.N_has_opr).
Instance N_has_mul : HasMul N := opr (HasOpr := Multiplicative.N_has_opr).

Instance N_has_zero : HasZero N := idn (HasIdn := Additive.N_has_idn).
Instance N_has_one : HasOne N := idn (HasIdn := Multiplicative.N_has_idn).

Instance N_is_left_distributive : IsLeftDistributive N.add N.mul := {}.
Proof. intros x y z. apply N.mul_add_distr_l. Qed.

Instance N_is_right_distributive : IsRightDistributive N.add N.mul := {}.
Proof. intros x y z. apply N.mul_add_distr_r. Qed.

Instance N_is_distributive : IsDistributive N.add N.mul := {}.

Instance N_is_semiring : IsSemiring N.add N.zero N.mul N.one := {}.

Definition N_hom (x : N) : N := (2 ^ x)%N.

Instance N_has_hom : HasHom N N := N_hom.

Instance N_is_setoid_homomorphism : IsSetoidHomomorphism N_hom := {}.

Instance N_is_semigroup_homomorphism :
  IsSemigroupHomomorphism N.add N.mul N_hom := {}.
Proof.
  intros x y. cbv -[N.add N.mul N.pow]. rewrite N.pow_add_r. reflexivity. Qed.

Instance N_is_monoid_homomorphism :
  IsMonoidHomomorphism N.add N.zero N.mul N.one N_hom := {}.
Proof. reflexivity. Qed.
