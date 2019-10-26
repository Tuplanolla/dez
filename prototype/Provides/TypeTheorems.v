From Maniunfold Require Export
  Init.
From Maniunfold.Is Require Import
  Isomorphism CommutativeSemiring CommutativeExponentialSemiring.
From Maniunfold.ShouldHave Require Import
  RelationNotations FieldNotations.

(* Section Context.

Context {A B : Type} `{is_isomorphism : IsIsomorphism A B}.

Instance isomorphism_has_hom : HasHom A B := fun x : A => hom (hom (hom x)).

Instance isomorphism_has_hom' : HasHom B A := fun x : B => hom (hom (hom x)).

Instance isomorphism_is_isomorphism :
  IsIsomorphism (A := B) (B := A) hom hom := {}.
Proof.
  - intros x. epose proof (B_preserving (hom x)). rewrite <- H.
    epose proof (A_preserving x). rewrite H0.
    apply B_preserving.
  - intros x. epose proof (A_preserving (hom x)). rewrite <- H.
    epose proof (B_preserving x). rewrite H0.
    apply A_preserving. Unshelve. apply B_has_eqv. Qed.

End Context. *)

Section Context.

Context {A : Type}.

Definition A_eqv (x y : A) : Prop := x = y.

Global Instance A_has_eqv : HasEqv A := A_eqv.

Global Instance A_is_reflexive : IsReflexive A_eqv := {}.
Proof. intros x. reflexivity. Qed.

Global Instance A_is_symmetric : IsSymmetric A_eqv := {}.
Proof. intros x y H. symmetry. apply H. Qed.

Global Instance A_is_transitive : IsTransitive A_eqv := {}.
Proof.
  intros x y z Hxy Hyz. etransitivity.
  - apply Hxy.
  - apply Hyz. Qed.

Global Instance A_is_setoid : IsSetoid A_eqv := {}.

End Context.

Definition Type_eqv (A B : Type) : Prop :=
  exists (f : A -> B) (g : B -> A), IsIsomorphism f g.

Instance Type_has_eqv : HasEqv Type := Type_eqv.

Instance Type_is_reflexive : IsReflexive Type_eqv := {}.
Proof.
  intros A. hnf. exists id, id.
  constructor. apply A_is_setoid. apply A_is_setoid.
  all: cbv; auto. Qed.

Instance Type_is_symmetric : IsSymmetric Type_eqv := {}.
Proof.
  intros A B H. hnf. destruct H as [f [g is_isomorphism]]. exists g, f.
  constructor. apply A_is_setoid. apply A_is_setoid. all: cbv.
  - intros x y H. apply f_equal. apply H.
  - intros x y H. apply f_equal. apply H.
  - intros x. apply B_preserving.
  - intros x. apply A_preserving. Qed.

Instance Type_is_transitive : IsTransitive Type_eqv := {}.
Proof.
  intros A B C HAB HBC. hnf.
  destruct HAB as [fAB [gBA A_B_is_isomorphism]],
    HBC as [fBC [gCB B_C_is_isomorphism]].
  exists (compose fBC fAB), (compose gBA gCB).
  constructor. apply A_is_setoid. apply A_is_setoid.
  - intros x y H. apply f_equal. apply H.
  - intros x y H. apply f_equal. apply H.
  - intros x. cbv. epose proof (B_preserving (fAB x)).
    assert (H' : gCB (fBC (fAB x)) == fAB x) by apply H.
    rewrite H. apply A_preserving.
  - intros x. cbv. epose proof (A_preserving (gCB x)).
    assert (H' : fAB (gBA (gCB x)) == gCB x) by apply H.
    rewrite H. apply B_preserving.
    Unshelve. all: try typeclasses eauto. Admitted.

Instance Type_is_setoid : IsSetoid Type_eqv := {}.

Module Additive.

Instance Type_has_opr : HasOpr Type := sum.

Instance Type_is_associative : IsAssociative sum := {}.
Proof. intros A B C.
eexists _. Unshelve. 2: { cbv. intros [a | [b | c]]; auto. }
eexists _. Unshelve. 2: { cbv. intros [[a | b] | c]; auto. }
constructor. 1-4: shelve.
cbv. intros [a | [b | c]]; auto.
cbv. intros [[a | b] | c]; auto.
Unshelve. 1-2: typeclasses eauto.
cbv. intros [a | [b | c]] [a' | [b' | c']]; intros; try inversion H; auto.
cbv. intros [[a | b] | c] [[a' | b'] | c']; intros; try inversion H; auto. Qed.

Instance Type_is_semigroup : IsSemigroup sum := {}.
Proof. intros A B H A' B' H'. hnf in *. Admitted.

Instance Type_has_idn : HasIdn Type := Empty_set.

Definition hom_left_identifier {A : Type} (x : Empty_set + A) : A :=
  match x with
  | inl x => match x with end
  | inr x => x
  end.

Definition cohom_left_identifier {A : Type} (x : A) : Empty_set + A :=
  inr Empty_set x.

Instance Type_is_left_identifiable : IsLeftIdentifiable sum Empty_set := {}.
Proof.
  intros A. exists hom_left_identifier, cohom_left_identifier.
  constructor. 1-4: admit. cbv.
  - intros [[] | x]. reflexivity.
  - intros x. reflexivity. Admitted.

Definition hom_right_identifier {A : Type} (x : A + Empty_set) : A :=
  match x with
  | inl x => x
  | inr x => match x with end
  end.

Definition cohom_right_identifier {A : Type} (x : A) : A + Empty_set :=
  inl Empty_set x.

Instance Type_is_right_identifiable : IsRightIdentifiable sum Empty_set := {}.
Proof.
  intros A. exists hom_right_identifier, cohom_right_identifier.
  constructor. 1-4: admit. cbv.
  - intros [x | []]. reflexivity.
  - intros x. reflexivity. Admitted.

Instance Type_is_identifier : IsBiidentifiable sum Empty_set := {}.

Instance Type_is_monoid : IsMonoid sum Empty_set := {}.

Definition hom_left_commutator {A B : Type} (x : A + B) : B + A :=
  match x with
  | inl x => inr x
  | inr x => inl x
  end.

Instance Type_is_commutative : IsCommutative sum := {}.
Proof. intros A B. cbv. exists hom_left_commutator, hom_left_commutator.
  constructor. 1-4: admit. cbv.
  - intros [x | y]; reflexivity.
  - intros [x | y]; reflexivity. Admitted.

Instance Type_is_commutative_monoid : IsCommutativeMonoid sum Empty_set := {}.

End Additive.

Module Multiplicative.

Instance Type_has_opr : HasOpr Type := prod.

Instance Type_is_associative : IsAssociative prod := {}.
Proof. Admitted.

Instance Type_is_semigroup : IsSemigroup prod := {}.
Proof. Admitted.

Instance Type_has_idn : HasIdn Type := unit.

Instance Type_is_left_identifiable : IsLeftIdentifiable prod unit := {}.
Proof. Admitted.

Instance Type_is_right_identifiable : IsRightIdentifiable prod unit := {}.
Proof. Admitted.

Instance Type_is_identifier : IsBiidentifiable prod unit := {}.

Instance Type_is_monoid : IsMonoid prod unit := {}.

Instance Type_is_commutative : IsCommutative prod := {}.
Proof. Admitted.

Instance Type_is_commutative_monoid : IsCommutativeMonoid prod unit := {}.

End Multiplicative.

Instance Type_has_add : HasAdd Type := sum.
Instance Type_has_mul : HasMul Type := prod.

Instance Type_has_zero : HasZero Type := Empty_set.
Instance Type_has_one : HasOne Type := unit.

Instance Type_is_left_distributive : IsLeftDistributive sum prod := {}.
Proof. Admitted.

Instance Type_is_right_distributive : IsRightDistributive sum prod := {}.
Proof. Admitted.

Instance Type_is_distributive : IsBidistributive sum prod := {}.

Instance Type_is_semiring : IsSemiring sum Empty_set prod unit := {}.

Instance Type_is_commutative_semiring :
  IsCommutativeSemiring sum Empty_set prod unit := {}.

Instance Type_is_exponential_semiring :
  IsExponentialSemiring sum Empty_set prod unit arrow := {}.
Proof. Admitted.

Instance Type_is_commutative_exponential_semiring :
  IsCommutativeExponentialSemiring sum Empty_set prod unit arrow := {}.
