(** * Morphism *)

From Maniunfold.Has Require Export
  BinaryRelation.

Class HasHom (A : Type) : Type := hom (x y : A) : Prop.

Typeclasses Transparent HasHom.
