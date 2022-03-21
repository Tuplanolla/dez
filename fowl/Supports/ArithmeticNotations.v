(** * Additive and Multiplicative Notations for Arithmetic Operations *)

From Coq Require Import
  ZArith.ZArith.
From DEZ.Has Require Import
  ArithmeticOperations ArithmeticActions Repetitions.
From DEZ.Is Require Import
  Involutive.
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

Module Unsigned.

Module Reified.

Record BoxN : Type := boxN {unboxN : N}.

Equations BoxN_of_Z (n : Z) : option BoxN :=
  BoxN_of_Z Z0 := Some (boxN N0);
  BoxN_of_Z (Zpos p) := Some (boxN (Npos p));
  BoxN_of_Z _ := None.

Equations Z_of_BoxN (x : BoxN) : option Z :=
  Z_of_BoxN (boxN N0) := Some Z0;
  Z_of_BoxN (boxN (Npos p)) := Some (Zpos p).

Module Notations.

#[local] Set Warnings "-numbers".

Context (A : Type)
  {X : HasEquivRel A} {x : HasZero A} {k : HasAdd A}
  {y : HasOne A} {m : HasMul A} (* `{!IsRing X x f k y m} *).

Number Notation A BoxN_of_Z Z_of_BoxN (via BoxN mapping [
  [of_N] => boxN]) : arithmetic_scope.

End Notations.

End Reified.

Export Reified.Notations.

End Unsigned.

Module Signed.

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

End Signed.

Export Signed.

Ltac unsign :=
  match goal with
  | |- context c [of_Z (Zneg ?p)] =>
    let a := context c [of_Z (Zneg p)] in
    let b := context c [neg (of_Z (Zpos p))] in
    change a with b
  | h : context c [of_Z (Zneg ?p)] |- _ =>
    let a := context c [of_Z (Zneg p)] in
    let b := context c [neg (of_Z (Zpos p))] in
    change a with b in h
  end.

Ltac sign :=
  match goal with
  | |- context c [neg (of_Z Z0)] =>
    let a := context c [neg (of_Z Z0)] in
    let b := context c [of_Z Z0] in
    replace (neg (of_Z Z0)) with (of_Z Z0)
  | |- context c [neg (of_Z (Zpos ?p))] =>
    let a := context c [neg (of_Z (Zpos p))] in
    let b := context c [of_Z (Zneg p)] in
    change a with b
  | |- context c [neg (of_Z (Zneg ?p))] =>
    let a := context c [neg (of_Z (Zneg p))] in
    let b := context c [of_Z (Zpos p)] in
    replace (neg (of_Z (Zneg p))) with (of_Z (Zpos p))
  | h : context c [neg (of_Z Z0)] |- _ =>
    let a := context c [neg (of_Z Z0)] in
    let b := context c [of_Z Z0] in
    replace (neg (of_Z Z0)) with (of_Z Z0) in h
  | h : context c [neg (of_Z (Zpos ?p))] |- _ =>
    let a := context c [neg (of_Z (Zpos p))] in
    let b := context c [of_Z (Zneg p)] in
    change a with b in h
  | h : context c [neg (of_Z (Zneg ?p))] |- _ =>
    let a := context c [neg (of_Z (Zneg p))] in
    let b := context c [of_Z (Zpos p)] in
    replace (neg (of_Z (Zneg p))) with (of_Z (Zpos p)) in h
  end.

#[local] Instance girp : IsGrp Z.eq Z.zero Z.opp Z.add.
Proof. Admitted.

Lemma ok `{!IsInvol _=_ -_}
  (a : - -0%arith = - (-0)%arith)
  (b : - -5%arith = - (-5)%arith) :
  - -5%arith = - (-5)%arith.
Proof.
  unsign. unsign. Fail unsign.
  sign. sign. sign. sign. sign. sign. sign. sign. Fail sign.
  2:{ rewrite <- (comm_act_ls_r (X := _=_) (f := neg) (al := Z_op) (bl := Z_op) (IsCommActLsR := z_op_un_op_is_two_l_bin_comm)). unsign. reflexivity. }
  change (- (-5)) with (- - (5)).
  unsign.
