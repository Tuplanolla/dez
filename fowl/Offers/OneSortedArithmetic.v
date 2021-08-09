From DEZ.Has Require Import
  Reciprocation.
From DEZ.Is Require Import
  Ring.
From DEZ.ShouldHave Require Import
  OneSortedArithmeticNotations.

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
