From DEZ.Has Require Export
  Arrow.

Class HasIden {A : Type} (has_arrow : HasArrow A) : Type :=
  iden : forall x : A, arrow x x.

Typeclasses Transparent HasIden.
