From Maniunfold.Is Require Import
  Ring.

Definition unit_eqv (x y : unit) : Prop := True.

Instance unit_has_eqv : HasEqv unit := unit_eqv.

Instance unit_is_reflexive : IsReflexive unit_eqv := {}.
Proof. intros x. constructor. Qed.

Instance unit_is_symmetric : IsSymmetric unit_eqv := {}.
Proof. intros x y p. constructor. Qed.

Instance unit_is_transitive : IsTransitive unit_eqv := {}.
Proof. intros x y z p q. constructor. Qed.

Instance unit_is_setoid : IsSetoid unit_eqv := {}.

Theorem unit_eqv_iff_eq : forall x y : unit,
  x == y <-> x = y.
Proof.
  intros [] []. split.
  - intros _. constructor.
  - intros _. constructor. Qed.

Definition tt2 (x y : unit) : unit := tt.

Instance unit_has_opr : HasOpr unit := tt2.

Instance unit_is_associative : IsAssociative tt2 := {}.
Proof. intros x y z. constructor. Qed.

Instance unit_is_semigroup : IsSemigroup tt2 := {}.
Proof. intros x y p z w q. constructor. Qed.

Instance unit_has_idn : HasIdn unit := tt.

Instance unit_is_left_identifiable : IsLeftIdentifiable tt2 tt := {}.
Proof. intros x. constructor. Qed.

Instance unit_is_right_identifiable : IsRightIdentifiable tt2 tt := {}.
Proof. intros x. constructor. Qed.

Instance unit_is_identifiable : IsIdentifiable tt2 tt := {}.

Instance unit_is_monoid : IsMonoid tt2 tt := {}.

Instance unit_is_commutative : IsCommutative tt2 := {}.
Proof. intros x y. constructor. Qed.

Instance unit_is_commutative_monoid : IsCommutativeMonoid tt2 tt := {}.

Definition tt1 (x : unit) : unit := tt.

Instance unit_has_inv : HasInv unit := tt1.

Instance unit_is_left_invertible : IsLeftInvertible tt2 tt tt1 := {}.
Proof. intros x. constructor. Qed.

Instance unit_is_right_invertible : IsRightInvertible tt2 tt tt1 := {}.
Proof. intros x. constructor. Qed.

Instance unit_is_invertible : IsInvertible tt2 tt tt1 := {}.

Instance unit_is_group : IsGroup tt2 tt tt1 := {}.
Proof. intros x y p. constructor. Qed.

Instance unit_is_abelian_group : IsAbelianGroup tt2 tt tt1 := {}.

Instance unit_has_add : HasAdd unit := tt2.
Instance unit_has_mul : HasMul unit := tt2.

Instance unit_has_zero : HasZero unit := tt.
Instance unit_has_one : HasOne unit := tt.

Instance unit_is_left_distributive : IsLeftDistributive tt2 tt2 := {}.
Proof. intros x y z. constructor. Qed.

Instance unit_is_right_distributive : IsRightDistributive tt2 tt2 := {}.
Proof. intros x y z. constructor. Qed.

Instance unit_is_distributive : IsDistributive tt2 tt2 := {}.

Instance unit_is_semiring : IsSemiring tt2 tt tt2 tt := {}.

Instance unit_has_neg : HasNeg unit := tt1.

Instance unit_is_ring : IsRing tt2 tt tt1 tt2 tt := {}.

Theorem unit_ring_trivial : 1 == 0.
Proof. reflexivity. Qed.
