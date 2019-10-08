From Maniunfold.Has Require Import EquivalenceRelation OrderRelation.
From Maniunfold.Is Require Import Reflexive Antisymmetric Transitive.

Class IsPartialOrder (A : Type)
  {has_eqv : HasEqv A} {has_ord : HasOrd A} : Prop := {
  ord_is_reflexive :> IsReflexive A;
  ord_is_antisymmetric :> IsAntisymmetric A;
  ord_is_transitive :> IsTransitive A;
}.
