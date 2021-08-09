From Coq Require Import
  ZArith.
From DEZ.Has Require Export
  GroupOperation.

Import Pos.

Definition popr {A : Type} {has_opr : HasOpr A} (n : positive) (x : A) : A :=
  iter_op opr n x.
