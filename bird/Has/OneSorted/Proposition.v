(* bad *)
From Maniunfold Require Export
  Init.

Class HasProp (A : Type) : Type := prop : A -> Prop.

Typeclasses Transparent HasProp.
