From Maniunfold.Has Require Export
  OneSorted.Addition OneSorted.Negation
  OneSorted.Multiplication OneSorted.Reciprocation.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Section Context.

Context (A : Type) `(HasAdd A) `(HasNeg A).

(** Subtraction, difference, minus. *)

Definition sub (x y : A) : A := x + (- y).

End Context.

Arguments sub {_ _ _} _ _.

Section Context.

Context (A : Type) `(HasMul A) `(HasRecip A).

(** Division, ratio, obelus. *)

Definition div (x y : A) : A := x * (/ y).

End Context.

Arguments div {_ _ _} _ _.
