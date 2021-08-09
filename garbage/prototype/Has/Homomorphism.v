From DEZ Require Export
  Init.

Class HasHom (A B : Type) : Type := hom : A -> B.

Typeclasses Transparent HasHom.
