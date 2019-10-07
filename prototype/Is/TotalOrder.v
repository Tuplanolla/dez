From Maniunfold.Has Require Import EquivalenceRelation OrderRelation.
From Maniunfold.Is Require Import Setoid Antisymmetric Transitive Connex.

Class IsTotalOrder (A : Type)
  {has_eqv : HasEqv A} {has_ord : HasOrd A} : Prop := {
  ord_is_antisymmetric :> IsAntisymmetric A;
  ord_is_transitive :> IsTransitive A;
  ord_is_connex :> IsConnex A;
}.
