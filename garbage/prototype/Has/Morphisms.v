From DEZ.Has Require Export
  Relation.

Class HasMorph (A : Type) : Type := morph : A -> A -> Prop.

Typeclasses Transparent HasMorph.

Global Instance morph_has_rel {A : Type} {has_morph : HasMorph A} : HasRel A :=
  morph.
