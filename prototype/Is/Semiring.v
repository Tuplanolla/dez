From Maniunfold.Has Require Import Relation EquivalenceRelation
  FieldOperations FieldIdentities.
From Maniunfold.Is Require Import Identifiable Distributive Transitive
  Setoid Semigroup Monoid CommutativeMonoid.

Class IsSemiring (A : Type) {has_eqv : HasEqv A}
  {has_add : HasAdd A} {has_zero : HasZero A}
  {has_mul : HasMul A} {has_one : HasOne A} : Prop := {
  add_is_commutative_monoid :> IsCommutativeMonoid A
    (has_opr := has_add) (has_idn := has_zero);
  mul_is_monoid :> IsMonoid A
    (has_opr := has_mul) (has_idn := has_one);
  mul_add_is_distributive :> IsDistributive A;
}.

Add Parametric Morphism {A : Type} `{is_semiring : IsSemiring A} : add
  with signature eqv ==> eqv ==> eqv
  as eqv_add_morphism.
Proof. intros x y p z w q. apply opr_proper; auto. Qed.

Add Parametric Morphism {A : Type} `{is_semiring : IsSemiring A} : mul
  with signature eqv ==> eqv ==> eqv
  as eqv_mul_morphism.
Proof. intros x y p z w q. apply opr_proper; auto. Qed.
