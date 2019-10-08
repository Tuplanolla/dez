From Coq Require Import ZArith.
From Maniunfold.Has Require Import EquivalenceRelation OrderRelation
  GroupOperation GroupIdentity GroupInverse
  FieldOperations FieldIdentities FieldInverses.
From Maniunfold.Is Require Import Reflexive Symmetric Transitive
  Antisymmetric Connex Associative Commutative Identity Inverse Distributive
  Setoid PartialOrder TotalOrder
  Semigroup Monoid CommutativeMonoid Group AbelianGroup Semiring Ring.

Module Equivalence.

Instance Z_has_eqv : HasEqv Z := fun x y : Z => x = y.

Instance Z_is_reflexive : IsReflexive Z := {}.
Proof. intros x. reflexivity. Qed.

Instance Z_is_symmetric : IsSymmetric Z := {}.
Proof. intros x y p. symmetry; auto. Qed.

Instance Z_is_transitive : IsTransitive Z := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Instance Z_is_setoid : IsSetoid Z := {}.

End Equivalence.

Module Order.

Instance Z_has_ord : HasOrd Z := fun x y : Z => (x <= y)%Z.

Instance Z_is_antisymmetric : IsAntisymmetric Z := {}.
Proof. intros x y p q. apply Z.le_antisymm; auto. Qed.

Instance Z_is_transitive : IsTransitive Z := {}.
Proof. intros x y z p q. transitivity y; auto. Qed.

Instance Z_is_connex : IsConnex Z := {}.
Proof. intros x y. apply Z.le_ge_cases. Qed.

Instance Z_is_total_order : IsTotalOrder Z := {}.

End Order.

Module Additive.

Instance Z_has_opr : HasOpr Z := fun x y : Z => (x + y)%Z.

Instance Z_is_associative : IsAssociative Z := {}.
Proof. intros x y z. apply Z.add_assoc. Qed.

Instance Z_is_semigroup : IsSemigroup Z := {}.

Instance Z_has_idn : HasIdn Z := 0%Z.

Instance Z_is_left_identity : IsLeftIdentity Z := {}.
Proof. intros x. apply Z.add_0_l. Qed.

Instance Z_is_right_identity : IsRightIdentity Z := {}.
Proof. intros x. apply Z.add_0_r. Qed.

Instance Z_is_identity : IsIdentity Z := {}.

Instance Z_is_monoid : IsMonoid Z := {}.

Instance Z_is_commutative : IsCommutative Z := {}.
Proof. intros x y. apply Z.add_comm. Qed.

Instance Z_is_commutative_monoid : IsCommutativeMonoid Z := {}.

Instance Z_has_inv : HasInv Z := fun x : Z => (- x)%Z.

Instance Z_is_left_inverse : IsLeftInverse Z := {}.
Proof. intros x. apply Z.add_opp_diag_l. Qed.

Instance Z_is_right_inverse : IsRightInverse Z := {}.
Proof. intros x. apply Z.add_opp_diag_r. Qed.

Instance Z_is_inverse : IsInverse Z := {}.

Instance Z_is_group : IsGroup Z := {}.

Instance Z_is_abelian_group : IsAbelianGroup Z := {}.

End Additive.

Module Multiplicative.

Instance Z_has_opr : HasOpr Z := fun x y : Z => (x * y)%Z.

Instance Z_is_associative : IsAssociative Z := {}.
Proof. intros x y z. apply Z.mul_assoc. Qed.

Instance Z_is_semigroup : IsSemigroup Z := {}.

Instance Z_has_idn : HasIdn Z := 1%Z.

Instance Z_is_left_identity : IsLeftIdentity Z := {}.
Proof. intros x. apply Z.mul_1_l. Qed.

Instance Z_is_right_identity : IsRightIdentity Z := {}.
Proof. intros x. apply Z.mul_1_r. Qed.

Instance Z_is_identity : IsIdentity Z := {}.

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

Instance Z_has_neg : HasNeg Z := inv.

Instance Z_is_ring : IsRing Z := {}.
