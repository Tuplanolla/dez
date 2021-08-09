From DEZ.Has Require Export
  Relation EquivalenceRelation.

Class HasOrd (A : Type) : Type := ord : A -> A -> Prop.

Typeclasses Transparent HasOrd.

Global Instance ord_has_rel {A : Type} {has_ord : HasOrd A} : HasRel A := ord.
