(** * Left and Right Action or Act *)

From Maniunfold Require Export
  Init.

Class HasActL (A B : Type) : Type := act_l (a : A) (x : B) : B.
Class HasActR (A B : Type) : Type := act_r (x : B) (a : A) : B.

Typeclasses Transparent HasActL HasActR.
