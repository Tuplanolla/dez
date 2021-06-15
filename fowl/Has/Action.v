(** * Action or Act *)

From Maniunfold Require Export
  Init.

Class HasActL (A B : Type) : Type := act_l : A -> B -> B.
Class HasActR (A B : Type) : Type := act_r : B -> A -> B.

Typeclasses Transparent HasActL HasActR.
