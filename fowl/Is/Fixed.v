From Maniunfold Require Export
  Init.

Class IsFixed (A : Type) (x : A) (f : A -> A) : Prop :=
  fixed : f x = x.
