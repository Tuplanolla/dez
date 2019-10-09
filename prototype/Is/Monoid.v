From Maniunfold.Has Require Import EquivalenceRelation
  GroupOperation GroupIdentity.
From Maniunfold.Is Require Import Semigroup Identifiable.

Class IsMonoid (A : Type)
  {has_eqv : HasEqv A} {has_opr : HasOpr A} {has_idn : HasIdn A} : Prop := {
  opr_is_semigroup :> IsSemigroup A;
  opr_is_identifiable :> IsIdentifiable A;
}.
