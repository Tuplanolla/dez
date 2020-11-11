From Maniunfold.Has Require Import
  OneSorted.Reciprocation.
From Maniunfold.Is Require Import
  OneSorted.Ring.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.

Section Context.

(** TODO Use [IsFld] instead. *)

Context (A : Type) `{IsRing A} `(HasRecip A).

(** Subtraction, difference, minus. *)

Definition sub (x y : A) : A := x + (- y).

(** Division, ratio, obelus. *)

Definition div (x y : A) : A := x * (/ y).

End Context.

Arguments sub {_} _ _ _ _ /.
Arguments div {_} _ _ _ _ /.
