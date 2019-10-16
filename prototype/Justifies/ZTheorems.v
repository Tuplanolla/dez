From Coq Require Import
  ZArith.
From Maniunfold.Is Require Import
  TotalOrder NontrivialRing MonoidHomomorphism.

Module Equivalence.

Definition Z_eqv (x y : Z) : Prop := x = y.

Instance Z_has_eqv : HasEqv Z := Z_eqv.

Instance Z_is_reflexive : IsReflexive Z_eqv := {}.
Proof. intros x. reflexivity. Qed.

Instance Z_is_symmetric : IsSymmetric Z_eqv := {}.
Proof. intros x y p. symmetry; auto. Qed.

Instance Z_is_transitive : IsTransitive Z_eqv := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Instance Z_is_setoid : IsSetoid Z := {}.

End Equivalence.

Module Order.

Definition Z_ord (x y : Z) : Prop := (x <= y)%Z.

Instance Z_has_ord : HasOrd Z := Z_ord.

Instance Z_is_antisymmetric : IsAntisymmetric Z_ord := {}.
Proof. intros x y p q. apply Z.le_antisymm; auto. Qed.

Instance Z_is_transitive : IsTransitive Z_ord := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Instance Z_is_connex : IsConnex Z_ord := {}.
Proof. intros x y. apply Z.le_ge_cases. Qed.

Instance Z_is_total_order : IsTotalOrder Z := {}.

End Order.

Module Additive.

Instance Z_has_opr : HasOpr Z := fun x y : Z => (x + y)%Z.

Instance Z_is_associative : IsAssociative Z := {}.
Proof. intros x y z. apply Z.add_assoc. Qed.

Instance Z_is_semigroup : IsSemigroup Z := {}.

Instance Z_has_idn : HasIdn Z := 0%Z.

Instance Z_is_left_identifiable : IsLeftIdentifiable Z := {}.
Proof. intros x. apply Z.add_0_l. Qed.

Instance Z_is_right_identifiable : IsRightIdentifiable Z := {}.
Proof. intros x. apply Z.add_0_r. Qed.

Instance Z_is_identifiable : IsIdentifiable Z := {}.

Instance Z_is_monoid : IsMonoid Z := {}.

Instance Z_is_commutative : IsCommutative Z := {}.
Proof. intros x y. apply Z.add_comm. Qed.

Instance Z_is_commutative_monoid : IsCommutativeMonoid Z := {}.

Instance Z_has_inv : HasInv Z := fun x : Z => (- x)%Z.

Instance Z_is_left_invertible : IsLeftInvertible Z := {}.
Proof. intros x. apply Z.add_opp_diag_l. Qed.

Instance Z_is_right_invertible : IsRightInvertible Z := {}.
Proof. intros x. apply Z.add_opp_diag_r. Qed.

Instance Z_is_invertible : IsInvertible Z := {}.

Instance Z_is_group : IsGroup Z := {}.

Instance Z_is_abelian_group : IsAbelianGroup Z := {}.

End Additive.

Module Multiplicative.

Instance Z_has_opr : HasOpr Z := fun x y : Z => (x * y)%Z.

Instance Z_is_associative : IsAssociative Z := {}.
Proof. intros x y z. apply Z.mul_assoc. Qed.

Instance Z_is_semigroup : IsSemigroup Z := {}.

Instance Z_has_idn : HasIdn Z := 1%Z.

Instance Z_is_left_identifiable : IsLeftIdentifiable Z := {}.
Proof. intros x. apply Z.mul_1_l. Qed.

Instance Z_is_right_identifiable : IsRightIdentifiable Z := {}.
Proof. intros x. apply Z.mul_1_r. Qed.

Instance Z_is_identifiable : IsIdentifiable Z := {}.

Instance Z_is_monoid : IsMonoid Z := {}.

Instance Z_is_commutative : IsCommutative Z := {}.
Proof. intros x y. apply Z.mul_comm. Qed.

Instance Z_is_commutative_monoid : IsCommutativeMonoid Z := {}.

End Multiplicative.

Instance Z_has_add : HasAdd Z := opr (HasOpr := Additive.Z_has_opr).
Instance Z_has_mul : HasMul Z := opr (HasOpr := Multiplicative.Z_has_opr).

Instance Z_has_zero : HasZero Z := idn (HasIdn := Additive.Z_has_idn).
Instance Z_has_one : HasOne Z := idn (HasIdn := Multiplicative.Z_has_idn).

Instance Z_is_left_distributive : IsLeftDistributive Z := {}.
Proof. intros x y z. apply Z.mul_add_distr_l. Qed.

Instance Z_is_right_distributive : IsRightDistributive Z := {}.
Proof. intros x y z. apply Z.mul_add_distr_r. Qed.

Instance Z_is_distributive : IsDistributive Z := {}.

Instance Z_is_semiring : IsSemiring Z := {}.

Instance Z_has_neg : HasNeg Z := inv (HasInv := Additive.Z_has_inv).

Instance Z_is_ring : IsRing Z := {}.

Instance Z_is_nontrivial_ring : IsNontrivialRing Z := {}.
Proof. intros H. inversion H. Qed.
