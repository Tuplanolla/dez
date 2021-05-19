From Maniunfold.Has Require Export
  Function.

Fail Fail Class IsInj (A B : Type) `(HasFn A B) : Prop :=
  inj (x y : A) (e : fn x = fn y) : x = y.

Notation IsInj := (Proper (eq <== eq)).
Notation inj := (proper_prf (R := eq <== eq) (m := fn)).
