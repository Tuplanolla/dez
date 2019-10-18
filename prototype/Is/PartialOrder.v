From Maniunfold.Has Require Export
  EquivalenceRelation OrderRelation.
From Maniunfold.Is Require Export
  Preorder Antisymmetric.

Class IsPartialOrder {A : Type} {has_eqv : HasEqv A}
  (has_ord : HasOrd A) : Prop := {
  partial_order_ord_is_preorder :> IsPreorder ord;
  partial_order_ord_is_antisymmetric :> IsAntisymmetric ord;
}.
