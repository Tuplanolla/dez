From Coq Require Import
  ZArith.
From Maniunfold.Has Require Export
  GroupOperation GroupIdentity GroupInverse.
From Maniunfold.Provides Require Import
  PositivePowers.

Definition zopr {A : Type} {has_opr : HasOpr A}
  {has_idn : HasIdn A} {has_inv : HasInv A} (n : Z) (x : A) : A :=
  match n with
  | Z0 => idn
  | Zpos p => popr p x
  | Zneg p => inv (popr p x)
  end.
