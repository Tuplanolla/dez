From Maniunfold.Has Require Import EquivalenceRelation Operation Identity.
From Maniunfold.Is Require Import Setoid Monoid Commutative.

Class CommutativeMonoid (A : Type)
  {has_eqv : HasEqv A} {has_opr : HasOpr A} {has_idn : HasIdn A} : Prop := {
  opr_is_monoid :> IsMonoid A;
  opr_commutative :> IsCommutative A;
}.
