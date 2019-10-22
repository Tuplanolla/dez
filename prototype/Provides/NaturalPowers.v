From Coq Require Import
  ZArith.
From Maniunfold.Has Require Export
  GroupOperation GroupIdentity.
From Maniunfold.Provides Require Import
  PositivePowers.

Definition nopr {A : Type} {has_opr : HasOpr A}
  {has_idn : HasIdn A} (n : N) (x : A) : A :=
  match n with
  | N0 => idn
  | Npos p => popr p x
  end.
