From DEZ Require Export
  Init.

Class HasDist (A S : Type) : Type := dist : A -> A -> S.

Typeclasses Transparent HasDist.
