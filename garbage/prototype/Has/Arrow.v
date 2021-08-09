From DEZ.Has Require Export
  Relation.

Class HasArrow (A : Type) : Type := arrow : A -> A -> Prop.

Typeclasses Transparent HasArrow.

Global Instance arrow_has_rel {A : Type} {has_arrow : HasArrow A} : HasRel A :=
  arrow.
