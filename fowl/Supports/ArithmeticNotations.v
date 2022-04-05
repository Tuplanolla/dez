(** * Additive and Multiplicative Notations for Arithmetic Operations *)

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

(** TODO ...and now for the good parts! *)

Module Positive.

Module Reified.

Variant positiveR : Type :=
  | xbR (n : positive) : positiveR
  | xHR : positiveR.

Equations positiveR_of_Z (n : Z) : option positiveR :=
  positiveR_of_Z (Zpos xH) := Some xHR;
  positiveR_of_Z (Zpos p) := Some (xbR p);
  positiveR_of_Z _ := None.

Equations Z_of_positiveR (n : positiveR) : Z :=
  Z_of_positiveR (xbR p) := Zpos p;
  Z_of_positiveR xHR := Zpos xH.

Module Notations.

#[local] Set Warnings "-numbers".

Context (A : Type)
  {k : HasAdd A} {y : HasOne A}.

Number Notation A positiveR_of_Z Z_of_positiveR (via positiveR mapping [
  [one] => xHR,
  [of_positive] => xbR]) : arithmetic_scope.

End Notations.

End Reified.

Export Reified.Notations.

End Positive.

Module Natural.

Module Reified.

Variant NR : Type :=
  | N0R : NR
  | N1R : NR
  | NposR (n : positive) : NR.

Equations NR_of_Z (n : Z) : option NR :=
  NR_of_Z Z0 := Some N0R;
  NR_of_Z (Zpos xH) := Some N1R;
  NR_of_Z (Zpos p) := Some (NposR p);
  NR_of_Z _ := None.

Equations Z_of_NR (n : NR) : Z :=
  Z_of_NR N0R := Z0;
  Z_of_NR N1R := Zpos xH;
  Z_of_NR (NposR p) := Zpos p.

Module Notations.

#[local] Set Warnings "-numbers".

Context (A : Type)
  {x : HasZero A} {k : HasAdd A} {y : HasOne A}.

Number Notation A NR_of_Z Z_of_NR (via NR mapping [
  [zero] => N0R,
  [one] => N1R,
  [of_positive] => NposR]) : arithmetic_scope.

End Notations.

End Reified.

Export Reified.Notations.

End Natural.

Module Integral.

Module Reified.

Variant ZR : Type :=
  | Z0R : ZR
  | Z1R : ZR
  | Zopp1R : ZR
  | ZposR (n : positive) : ZR
  | ZnegR (n : positive) : ZR.

Equations ZR_of_Z (n : Z) : ZR :=
  ZR_of_Z Z0 := Z0R;
  ZR_of_Z (Zpos xH) := Z1R;
  ZR_of_Z (Zneg xH) := Zopp1R;
  ZR_of_Z (Zpos p) := ZposR p;
  ZR_of_Z (Zneg p) := ZnegR p.

Equations Z_of_ZR (n : ZR) : Z :=
  Z_of_ZR Z0R := Z0;
  Z_of_ZR Z1R := Zpos xH;
  Z_of_ZR Zopp1R := Zneg xH;
  Z_of_ZR (ZposR p) := Zpos p;
  Z_of_ZR (ZnegR p) := Zneg p.

Module Notations.

#[local] Set Warnings "-numbers".

Context (A : Type)
  {x : HasZero A} {f : HasNeg A} {k : HasAdd A} {y : HasOne A}.

Number Notation A ZR_of_Z Z_of_ZR (via ZR mapping [
  [zero] => Z0R,
  [one] => Z1R,
  [negative_one] => Zopp1R,
  [of_positive] => ZposR,
  [of_negative] => ZnegR]) : arithmetic_scope.

End Notations.

End Reified.

Export Reified.Notations.

End Integral.

Export Integral.
