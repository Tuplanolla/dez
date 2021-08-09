From DEZ.Has Require Export
  Arrow.

Class HasComp {A : Type} (has_arrow : HasArrow A) : Type :=
  comp : forall x y z : A, arrow x y -> arrow y z -> arrow x z.

Typeclasses Transparent HasComp.
