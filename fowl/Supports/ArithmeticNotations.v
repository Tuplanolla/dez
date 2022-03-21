(** * Additive and Multiplicative Notations for Algebraic Operations *)

From Coq Require Import
  ZArith.ZArith.
From DEZ.Has Require Import
  ArithmeticOperations ArithmeticActions Repetitions.

Reserved Notation "x '*<' y" (left associativity, at level 40).
Reserved Notation "x '>*' y" (left associativity, at level 40).

Declare Scope arithmetic_scope.
Delimit Scope arithmetic_scope with arith.

#[global] Open Scope arithmetic_scope.

Notation "'-_'" := neg : arithmetic_scope.
Notation "'-' x" := (neg x) : arithmetic_scope.
Notation "'_+_'" := add : arithmetic_scope.
Notation "x '+' y" := (add x y) : arithmetic_scope.
Notation "'/_'" := recip : arithmetic_scope.
Notation "'/' x" := (recip x) : arithmetic_scope.
Notation "'_*_'" := mul : arithmetic_scope.
Notation "x '*' y" := (mul x y) : arithmetic_scope.
Notation "'_*<_'" := s_mul_l : arithmetic_scope.
Notation "a '*<' x" := (s_mul_l a x) : arithmetic_scope.
Notation "'_>*_'" := s_mul_r : arithmetic_scope.
Notation "x '>*' a" := (s_mul_r x a) : arithmetic_scope.

(** ...and now for the good parts! *)

(** This has only 0 and 1. *)

(* Module Reified.

Equations bool_of_Z (n : Z) : option bool :=
  bool_of_Z Z0 := Some false;
  bool_of_Z (Zpos xH) := Some true;
  bool_of_Z _ := None.

Equations Z_of_bool (x : bool) : option Z :=
  Z_of_bool true := Some (Zpos xH);
  Z_of_bool false := Some Z0.

Module Notations.

#[local] Set Warnings "-numbers".

Context (A : Type) {x : HasNullOp A}.

Number Notation A bool_of_Z Z_of_bool (via bool mapping [
  [zero] => false,
  [one] => true]) : arithmetic_scope.

End Notations.

End Reified.

Export Reified.Notations. *)

Module Reified.

Record BoxZ : Type := boxZ {unboxZ : Z}.

Module Notations.

#[local] Set Warnings "-numbers".

Context (A : Type)
  {X : HasEquivRel A} {x : HasZero A} {f : HasNeg A} {k : HasAdd A}
  {y : HasOne A} {m : HasMul A} (* `{!IsRing X x f k y m} *).

Number Notation A boxZ unboxZ (via BoxZ mapping [
  [of_Z] => boxZ]) : arithmetic_scope.

End Notations.

End Reified.

Export Reified.Notations.
