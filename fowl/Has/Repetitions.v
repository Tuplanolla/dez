(** * Integer Repetitions (Multiples and Powers) *)

From Coq Require Import
  PArith.PArith NArith.NArith ZArith.ZArith.
From DEZ.Has Require Export
  Operations ArithmeticOperations.

(** The notation [(- 3) * y] corresponding to the expression [Z_op (- 3) y]
    represents repeating the element [y] three times and
    inverting the result, producing
    [(- y) + (- y) + (- y)] or [- (y + y + y)],
    up to associativity and distributivity.
    This kind of repetition can be performed
    in semigroups, monoids and groups. *)

Section Context.

Context (A : Type)
  {k : HasBinOp A}.

Import Pos.

(** Repeat a semigroup element by a positive integer. *)

Equations positive_op (n : positive) (y : A) : A :=
  positive_op n y := iter_op k n y.

End Context.

Section Context.

Context (A : Type)
  {x : HasNullOp A} {k : HasBinOp A}.

(** Repeat a monoid element by a natural number. *)

Equations nat_op (n : nat) (y : A) : A :=
  nat_op O y := x;
  nat_op (S p) y := k y (nat_op p y).

Equations N_op (n : N) (y : A) : A :=
  N_op N0 y := x;
  N_op (Npos p) y := positive_op p y.

End Context.

Section Context.

Context (A : Type)
  {x : HasNullOp A} {f : HasUnOp A} {k : HasBinOp A}.

(** Repeat a group element by an integer. *)

Equations Z_op (n : Z) (y : A) : A :=
  Z_op Z0 y := x;
  Z_op (Zpos p) y := positive_op p y;
  Z_op (Zneg p) y := f (positive_op p y).

End Context.

(** The notation [- 3] corresponding to the expression [of_Z (- 3)]
    represents embedding the integer [- 3] or
    repeating the unital element three times and inverting the result,
    producing [(- 1) + (- 1) + (- 1)] or [- (1 + 1 + 1)],
    up to associativity and distributivity.
    This kind of embedding or repetition can be performed
    in semirings and rings. *)

Section Context.

Context (A : Type)
  {x : HasZero A} {k : HasAdd A} {y : HasOne A}.

#[local] Instance positive_has_bin_op : HasBinOp A := k.

(** Embed a positive integer into a semiring. *)

Equations of_positive (n : positive) : A :=
  of_positive n := positive_op n y.

End Context.

Section Context.

Context (A : Type)
  {x : HasZero A} {k : HasAdd A} {y : HasOne A}.

#[local] Instance N_has_null_op : HasNullOp A := x.
#[local] Instance N_has_bin_op : HasBinOp A := k.

(** Embed a natural number into a semiring. *)

Equations of_nat (n : nat) : A :=
  of_nat n := nat_op n y.

Equations of_N (n : N) : A :=
  of_N n := N_op n y.

End Context.

Section Context.

Context (A : Type)
  {x : HasZero A} {f : HasNeg A} {k : HasAdd A} {y : HasOne A}.

#[local] Instance Z_has_null_op : HasNullOp A := x.
#[local] Instance Z_has_un_op : HasUnOp A := f.
#[local] Instance Z_has_bin_op : HasBinOp A := k.

(** Embed an integer into a ring. *)

Equations of_Z (n : Z) : A :=
  of_Z n := Z_op n y.

(** Embed negative one into a ring. *)

Equations negative_one : A :=
  negative_one := f one.

(** Embed a negative integer into a ring. *)

Equations of_negative (n : positive) : A :=
  of_negative n := f (of_positive n).

End Context.

(** The number notations [(- 3)] and [- (3)] corresponding
    to the expressions [of_Z (Zneg (xI xH))] and [neg (of_Z (Zpos (xI xH)))]
    repsectively are distinct yet convertible.
    The following tactics implement
    both directions of this conversion. *)

(** Convert one occurrence of [- (n)] into [(- n)]. *)

Ltac sign_once :=
  match goal with
  | |- context c [neg (of_Z (Zpos ?p))] =>
    let a := context c [neg (of_Z (Zpos p))] in
    let b := context c [of_Z (Zneg p)] in
    change a with b
  | |- context c [neg (of_positive ?p)] =>
    let a := context c [neg (of_positive p)] in
    let b := context c [of_negative p] in
    change a with b
  | h : context c [neg (of_Z (Zpos ?p))] |- _ =>
    let a := context c [neg (of_Z (Zpos p))] in
    let b := context c [of_Z (Zneg p)] in
    change a with b in h
  | h : context c [neg (of_positive ?p)] |- _ =>
    let a := context c [neg (of_positive p)] in
    let b := context c [of_negative p] in
    change a with b in h
  end.

(** Convert all occurrences of [- (n)] into [(- n)]. *)

Ltac sign := repeat sign_once.

(** Convert one occurrence of [(- n)] into [- (n)]. *)

Ltac unsign_once :=
  match goal with
  | |- context c [of_Z (Zneg ?p)] =>
    let a := context c [of_Z (Zneg p)] in
    let b := context c [neg (of_Z (Zpos p))] in
    change a with b
  | |- context c [of_negative ?p] =>
    let a := context c [of_negative p] in
    let b := context c [neg (of_positive p)] in
    change a with b
  | h : context c [of_Z (Zneg ?p)] |- _ =>
    let a := context c [of_Z (Zneg p)] in
    let b := context c [neg (of_Z (Zpos p))] in
    change a with b in h
  | h : context c [of_negative ?p] |- _ =>
    let a := context c [of_negative ?p] in
    let b := context c [neg (of_positive p)] in
    change a with b in h
  end.

(** Convert all occurrences of [(- n)] into [- (n)]. *)

Ltac unsign := repeat unsign_once.
