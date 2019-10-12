From Coq Require Import ZArith.
From Maniunfold.Is Require Import
  TotalOrder Ring MonoidHomomorphism.

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

(** TODO This is actually only true for nonnegative [Z],
    but let us pretend this is true for all [Z]
    until [N] gets its own treatment. *)

Instance Z_has_hom : HasHom Z Z := fun x : Z => (2 ^ x)%Z.

Instance Z_is_setoid_homomorphism : IsSetoidHomomorphism Z Z := {}.

Instance Z_is_semigroup_homomorphism : IsSemigroupHomomorphism Z Z
  (A_has_opr := add) (B_has_opr := mul) := {}.
Proof.
  intros x y. cbv [opr hom Z_has_hom].
  repeat rewrite <- two_p_equiv. apply two_p_is_exp.
  - assert (0 <= x)%Z by admit; auto.
  - assert (0 <= y)%Z by admit; auto. Admitted.

Instance Z_is_monoid_homomorphism : IsMonoidHomomorphism Z Z
  (A_has_opr := add) (A_has_idn := zero)
  (B_has_opr := mul) (B_has_idn := one) := {}.
Proof. cbv [idn]. reflexivity. Qed.
