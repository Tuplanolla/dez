From Maniunfold.Has Require Export
  Arrow.

Class HasHiEqv {A : Type} (has_arrow : HasArrow A) : Type :=
  hieqv : forall {x y : A}, arrow x y -> arrow x y -> Prop.

Typeclasses Transparent HasHiEqv.
