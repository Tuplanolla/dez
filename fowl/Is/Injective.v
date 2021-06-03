(** * Injectivity of a Function *)

From Maniunfold Require Export
  Init.

Fail Fail Class IsInj (A B : Type) (f : A -> B) : Prop :=
  inj (x y : A) (e : f x = f y) : x = y.

Notation IsInj f := (Proper (_=_ <== _=_) f).
Notation inj := (proper_prf : IsInj _).
