From DEZ Require Export
  Init.

Class HasRel (A : Type) : Type := rel : A -> A -> Prop.

Typeclasses Transparent HasRel.
