(** * Integer Multiples and Powers *)

From Coq Require Import
  PArith.PArith NArith.NArith ZArith.ZArith.
From DEZ.Has Require Export
  EquivalenceRelations Operations ArithmeticOperations.
(* From DEZ.Is Require Export
  Semigroup Monoid Group Ring. *)

Section Context.

Context (A : Type)
  {X : HasEquivRel A} {k : HasBinOp A}
  (* `{!IsSemigrp X k} *).

Import Pos.

Equations positive_op (n : positive) (y : A) : A :=
  positive_op n y := iter_op k n y.

End Context.

Section Context.

Context (A : Type)
  {X : HasEquivRel A} {x : HasNullOp A} {k : HasBinOp A}
  (* `{!IsMon X x k} *).

Equations nat_op (n : nat) (y : A) : A :=
  nat_op O y := x;
  nat_op (S p) y := k y (nat_op p y).

Equations N_op (n : N) (y : A) : A :=
  N_op N0 y := x;
  N_op (Npos p) y := positive_op p y.

End Context.

Section Context.

Context (A : Type)
  {X : HasEquivRel A} {x : HasNullOp A} {f : HasUnOp A} {k : HasBinOp A}
  (* `{!IsGrp X x f k} *).

Equations Z_op (n : Z) (y : A) : A :=
  Z_op Z0 y := x;
  Z_op (Zpos p) y := positive_op p y;
  Z_op (Zneg p) y := f (positive_op p y).

End Context.

Section Context.

Context (A : Type)
  {X : HasEquivRel A} {x : HasZero A} {f : HasNeg A} {k : HasAdd A}
  {y : HasOne A} {m : HasMul A} (* `{!IsRing X x f k y m} *).

#[local] Instance has_null_op : HasNullOp A := x.
#[local] Instance has_un_op : HasUnOp A := f.
#[local] Instance has_bin_op : HasBinOp A := k.

Equations of_Z (n : Z) : A :=
  of_Z n := Z_op n y.

End Context.
