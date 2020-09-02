From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Negation
  OneSorted.Multiplication OneSorted.Reciprocation.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Section Context.

Context {A : Type} {A_has_add : HasAdd A} {A_has_neg : HasNeg A}.

(** Subtraction, difference, minus. *)

Definition sub (x y : A) : A := x + (- y).

End Context.

Section Context.

Context {A : Type} {A_has_mul : HasMul A} {A_has_recip : HasRecip A}.

(** Division, ratio, obelus. *)

Definition div (x y : A) : A := x * (/ y).

End Context.
