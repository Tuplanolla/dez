From Coq Require Import
  ZArith.
From Maniunfold.Is Require Import
  TotalOrder NontrivialRing MonoidHomomorphism.

Module Equivalence.

Instance Z_has_eqv : HasEqv Z := Z.eq.

Instance Z_is_reflexive : IsReflexive Z.eq := {}.
Proof. intros x. reflexivity. Qed.

Instance Z_is_symmetric : IsSymmetric Z.eq := {}.
Proof. intros x y p. symmetry; auto. Qed.

Instance Z_is_transitive : IsTransitive Z.eq := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Instance Z_is_setoid : IsSetoid Z.eq := {}.

End Equivalence.

Module Order.

Instance Z_has_ord : HasOrd Z := Z.le.

Instance Z_is_antisymmetric : IsAntisymmetric Z.le := {}.
Proof. intros x y p q. apply Z.le_antisymm; auto. Qed.

Instance Z_is_transitive : IsTransitive Z.le := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Instance Z_is_connex : IsConnex Z.le := {}.
Proof. intros x y. apply Z.le_ge_cases. Qed.

Instance Z_is_total_order : IsTotalOrder Z.le := {}.

End Order.

Module Additive.

Instance Z_has_opr : HasOpr Z := Z.add.

Instance Z_is_associative : IsAssociative Z.add := {}.
Proof. intros x y z. apply Z.add_assoc. Qed.

Instance Z_is_semigroup : IsSemigroup Z.add := {}.

Instance Z_has_idn : HasIdn Z := Z.zero.

Instance Z_is_left_identifiable : IsLeftIdentifiable Z.add Z.zero := {}.
Proof. intros x. apply Z.add_0_l. Qed.

Instance Z_is_right_identifiable : IsRightIdentifiable Z.add Z.zero := {}.
Proof. intros x. apply Z.add_0_r. Qed.

Instance Z_is_identifiable : IsIdentifiable Z.add Z.zero := {}.

Instance Z_is_monoid : IsMonoid Z.add Z.zero := {}.

Instance Z_is_commutative : IsCommutative Z.add := {}.
Proof. intros x y. apply Z.add_comm. Qed.

Instance Z_is_commutative_monoid : IsCommutativeMonoid Z.add Z.zero := {}.

Instance Z_has_inv : HasInv Z := Z.opp.

Instance Z_is_left_invertible : IsLeftInvertible Z.add Z.zero Z.opp := {}.
Proof. intros x. apply Z.add_opp_diag_l. Qed.

Instance Z_is_right_invertible : IsRightInvertible Z.add Z.zero Z.opp := {}.
Proof. intros x. apply Z.add_opp_diag_r. Qed.

Instance Z_is_invertible : IsInvertible Z.add Z.zero Z.opp := {}.

Instance Z_is_group : IsGroup Z.add Z.zero Z.opp := {}.

Instance Z_is_abelian_group : IsAbelianGroup Z.add Z.zero Z.opp := {}.

End Additive.

Module Multiplicative.

Instance Z_has_opr : HasOpr Z := Z.mul.

Instance Z_is_associative : IsAssociative Z.mul := {}.
Proof. intros x y z. apply Z.mul_assoc. Qed.

Instance Z_is_semigroup : IsSemigroup Z.mul := {}.

Instance Z_has_idn : HasIdn Z := Z.one.

Instance Z_is_left_identifiable : IsLeftIdentifiable Z.mul Z.one := {}.
Proof. intros x. apply Z.mul_1_l. Qed.

Instance Z_is_right_identifiable : IsRightIdentifiable Z.mul Z.one := {}.
Proof. intros x. apply Z.mul_1_r. Qed.

Instance Z_is_identifiable : IsIdentifiable Z.mul Z.one := {}.

Instance Z_is_monoid : IsMonoid Z.mul Z.one := {}.

Instance Z_is_commutative : IsCommutative Z.mul := {}.
Proof. intros x y. apply Z.mul_comm. Qed.

Instance Z_is_commutative_monoid : IsCommutativeMonoid Z.mul Z.one := {}.

End Multiplicative.

Instance Z_has_add : HasAdd Z := Z.add.
Instance Z_has_mul : HasMul Z := Z.mul.

Instance Z_has_zero : HasZero Z := Z.zero.
Instance Z_has_one : HasOne Z := Z.one.

Instance Z_is_left_distributive : IsLeftDistributive Z.add Z.mul := {}.
Proof. intros x y z. apply Z.mul_add_distr_l. Qed.

Instance Z_is_right_distributive : IsRightDistributive Z.add Z.mul := {}.
Proof. intros x y z. apply Z.mul_add_distr_r. Qed.

Instance Z_is_distributive : IsDistributive Z.add Z.mul := {}.

Instance Z_is_semiring : IsSemiring Z.add Z.zero Z.mul Z.one := {}.

Instance Z_has_neg : HasNeg Z := Z.opp.

Instance Z_is_ring : IsRing Z.add Z.zero Z.opp Z.mul Z.one := {}.

Instance Z_is_nontrivial_ring :
  IsNontrivialRing Z.add Z.zero Z.opp Z.mul Z.one := {}.
Proof. intros H. inversion H. Qed.
