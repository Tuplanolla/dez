From Maniunfold.Is Require Import
  LeftModule.

Definition unit_eqv (x y : unit) : Prop := True.

Global Instance : HasEqv unit := unit_eqv.

Global Instance : IsReflexive unit_eqv := {}.
Proof. intros x. constructor. Qed.

Global Instance : IsSymmetric unit_eqv := {}.
Proof. intros x y p. constructor. Qed.

Global Instance : IsTransitive unit_eqv := {}.
Proof. intros x y z p q. constructor. Qed.

Global Instance : IsSetoid unit_eqv := {}.

Theorem unit_eqv_iff_eq : forall x y : unit,
  x == y <-> x = y.
Proof.
  intros [] []. split.
  - intros _. constructor.
  - intros _. constructor. Qed.

Definition tt2 (x y : unit) : unit := tt.

Global Instance : HasOpr unit := tt2.

Global Instance : IsAssociative tt2 := {}.
Proof. intros x y z. constructor. Qed.

Global Instance : IsSemigroup tt2 := {}.
Proof. intros x y p z w q. constructor. Qed.

Global Instance : HasIdn unit := tt.

Global Instance : IsLeftIdentifiable tt2 tt := {}.
Proof. intros x. constructor. Qed.

Global Instance : IsRightIdentifiable tt2 tt := {}.
Proof. intros x. constructor. Qed.

Global Instance : IsIdentifiable tt2 tt := {}.

Global Instance : IsMonoid tt2 tt := {}.

Global Instance : IsCommutative tt2 := {}.
Proof. intros x y. constructor. Qed.

Global Instance : IsCommutativeMonoid tt2 tt := {}.

Definition tt1 (x : unit) : unit := tt.

Global Instance : HasInv unit := tt1.

Global Instance : IsLeftInvertible tt2 tt tt1 := {}.
Proof. intros x. constructor. Qed.

Global Instance : IsRightInvertible tt2 tt tt1 := {}.
Proof. intros x. constructor. Qed.

Global Instance : IsInvertible tt2 tt tt1 := {}.

Global Instance : IsGroup tt2 tt tt1 := {}.
Proof. intros x y p. constructor. Qed.

Global Instance : IsAbelianGroup tt2 tt tt1 := {}.

Global Instance : HasAdd unit := tt2.
Global Instance : HasMul unit := tt2.

Global Instance : HasZero unit := tt.
Global Instance : HasOne unit := tt.

Global Instance : IsLeftDistributive tt2 tt2 := {}.
Proof. intros x y z. constructor. Qed.

Global Instance : IsRightDistributive tt2 tt2 := {}.
Proof. intros x y z. constructor. Qed.

Global Instance : IsDistributive tt2 tt2 := {}.

Global Instance : IsSemiring tt2 tt tt2 tt := {}.

Global Instance : HasNeg unit := tt1.

Global Instance : IsRing tt2 tt tt1 tt2 tt := {}.

Theorem unit_ring_trivial : 1 == 0.
Proof. reflexivity. Qed.

Section Context.

Context {S : Type} `{is_ring : IsRing S}.

Definition unit_lsmul (x : S) (y : unit) : unit := y.

Global Instance : HasLSMul S unit := unit_lsmul.

Global Instance : IsLeftModule add zero neg mul one
  tt2 tt tt1 unit_lsmul := {}.
Proof. all: constructor. Qed.

End Context.
