From Maniunfold.Is Require Import
  Ring.

Instance unit_has_eqv : HasEqv unit := fun x y : unit => True.

Instance unit_is_reflexive : IsReflexive unit := {}.
Proof. intros x. constructor. Qed.

Instance unit_is_symmetric : IsSymmetric unit := {}.
Proof. intros x y p. constructor. Qed.

Instance unit_is_transitive : IsTransitive unit := {}.
Proof. intros x y z p q. constructor. Qed.

Instance unit_is_setoid : IsSetoid unit := {}.

Instance unit_has_opr : HasOpr unit := fun x y : unit => tt.

Instance unit_is_associative : IsAssociative unit := {}.
Proof. intros x y z. constructor. Qed.

Instance unit_is_semigroup : IsSemigroup unit := {}.
Proof. intros x y p z w q. constructor. Qed.

Instance unit_has_idn : HasIdn unit := tt.

Instance unit_is_left_identifiable : IsLeftIdentifiable unit := {}.
Proof. intros x. constructor. Qed.

Instance unit_is_right_identifiable : IsRightIdentifiable unit := {}.
Proof. intros x. constructor. Qed.

Instance unit_is_identifiable : IsIdentifiable unit := {}.

Instance unit_is_monoid : IsMonoid unit := {}.

Instance unit_is_commutative : IsCommutative unit := {}.
Proof. intros x y. constructor. Qed.

Instance unit_is_commutative_monoid : IsCommutativeMonoid unit := {}.

Instance unit_has_inv : HasInv unit := fun x : unit => tt.

Instance unit_is_left_invertible : IsLeftInvertible unit := {}.
Proof. intros x. constructor. Qed.

Instance unit_is_right_invertible : IsRightInvertible unit := {}.
Proof. intros x. constructor. Qed.

Instance unit_is_invertible : IsInvertible unit := {}.

Instance unit_is_group : IsGroup unit := {}.
Proof. intros x y p. constructor. Qed.

Instance unit_is_abelian_group : IsAbelianGroup unit := {}.

Instance unit_has_add : HasAdd unit := opr.
Instance unit_has_mul : HasMul unit := opr.

Instance unit_has_zero : HasZero unit := idn.
Instance unit_has_one : HasOne unit := idn.

Instance unit_is_left_distributive : IsLeftDistributive unit := {}.
Proof. intros x y z. constructor. Qed.

Instance unit_is_right_distributive : IsRightDistributive unit := {}.
Proof. intros x y z. constructor. Qed.

Instance unit_is_distributive : IsDistributive unit := {}.

Instance unit_is_semiring : IsSemiring unit := {}.

Instance unit_has_neg : HasNeg unit := inv.

Instance unit_is_ring : IsRing unit := {}.

Theorem unit_ring_trivial : 1 == 0.
Proof. reflexivity. Qed.
