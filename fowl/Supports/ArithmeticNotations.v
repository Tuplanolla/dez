(** * Additive and Multiplicative Notations for Arithmetic Operations *)

From Coq Require Import
  ZArith.ZArith.
From DEZ.Has Require Import
  ArithmeticOperations ArithmeticActions Repetitions.
From DEZ.Is Require Import
  Involutive Absorbing.
From DEZ.Justifies Require Import
  IntegerPowerTheorems.

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

Module Designed.

Module Reified.

Record Boxpositive : Type := boxpositive {unboxpositive : positive}.

Equations Boxpositive_of_Z (n : Z) : option Boxpositive :=
  Boxpositive_of_Z (Zpos p) := Some (boxpositive p);
  Boxpositive_of_Z _ := None.

Equations Z_of_Boxpositive (n : Boxpositive) : option Z :=
  Z_of_Boxpositive (boxpositive p) := Some (Zpos p).

Module Notations.

#[local] Set Warnings "-numbers".

Context (A : Type)
  {k : HasAdd A} {y : HasOne A}.

Number Notation A Boxpositive_of_Z Z_of_Boxpositive (via Boxpositive mapping [
  [of_positive] => boxpositive]) : arithmetic_scope.

End Notations.

End Reified.

Export Reified.Notations.

End Designed.

Module Unsigned.

Module Reified.

Equations N_of_Z (n : Z) : option N :=
  N_of_Z Z0 := Some N0;
  N_of_Z (Zpos p) := Some (Npos p);
  N_of_Z _ := None.

Equations Z_of_N (n : N) : Z :=
  Z_of_N N0 := Z0;
  Z_of_N (Npos p) := Zpos p.

Module Notations.

#[local] Set Warnings "-numbers".

Context (A : Type)
  {x : HasZero A} {k : HasAdd A} {y : HasOne A}.

Number Notation A N_of_Z Z_of_N (via N mapping [
  [zero] => N0,
  [of_positive] => Npos]) : arithmetic_scope.

End Notations.

End Reified.

Export Reified.Notations.

End Unsigned.

Module Signed.

Module Reified.

Equations Z_of_Z (n : Z) : Z :=
  Z_of_Z n := n.

Module Notations.

#[local] Set Warnings "-numbers".

Section Context.

Context (A : Type)
  {x : HasZero A} {f : HasNeg A} {k : HasAdd A} {y : HasOne A}.

(** TODO Do it better! *)

Equations of_negative (n : positive) : A :=
  of_negative n := f (of_positive n).

End Context.

Context (A : Type)
  {x : HasZero A} {f : HasNeg A} {k : HasAdd A} {y : HasOne A}.

Number Notation A Z_of_Z Z_of_Z (via Z mapping [
  [zero] => Z0,
  [of_positive] => Zpos,
  [of_negative] => Zneg]) : arithmetic_scope.

End Notations.

End Reified.

Export Reified.Notations.

End Signed.

Export Signed.
