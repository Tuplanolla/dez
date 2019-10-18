From Maniunfold Require Export
  Init.
From Maniunfold.Has Require Export
  EquivalenceRelation OrderRelation.
From Maniunfold.Is Require Export
  Proper Reflexive Transitive.

Class IsPreorder {A : Type} {has_eqv : HasEqv A}
  (has_ord : HasOrd A) : Prop := {
  preorder_ord_is_proper :> IsProper (eqv ==> eqv ==> flip impl) ord;
  preorder_ord_is_reflexive :> IsReflexive ord;
  preorder_ord_is_transitive :> IsTransitive ord;
}.
