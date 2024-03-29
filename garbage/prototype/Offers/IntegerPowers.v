From Coq Require Import
  ZArith.
From DEZ.Has Require Export
  GroupOperation GroupIdentity GroupInverse.
From DEZ.Offers Require Import
  PositivePowers.
From DEZ.ShouldHave Require Import
  AdditiveGroupNotations.

Definition zopr {A : Type} {has_opr : HasOpr A}
  {has_idn : HasIdn A} {has_inv : HasInv A} (n : Z) (x : A) : A :=
  match n with
  | Z0 => 0
  | Zpos p => popr p x
  | Zneg p => - (popr p x)
  end.
