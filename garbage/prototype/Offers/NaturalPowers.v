From Coq Require Import
  ZArith.
From DEZ.Has Require Export
  GroupOperation GroupIdentity.
From DEZ.Offers Require Import
  PositivePowers.
From DEZ.ShouldHave Require Import
  AdditiveGroupNotations.

Definition nopr {A : Type} {has_opr : HasOpr A}
  {has_idn : HasIdn A} (n : N) (x : A) : A :=
  match n with
  | N0 => 0
  | Npos p => popr p x
  end.
