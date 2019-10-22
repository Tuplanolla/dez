From Coq Require Import
  ZArith.
From Maniunfold Require Export
  Init.
From Maniunfold.Is Require Import
  Group.

Import Pos.

Definition popr {A : Type} `{is_semigroup : IsSemigroup A}
  (n : positive) (x : A) : A :=
  iter_op opr n x.

Definition nopr {A : Type} `{is_monoid : IsMonoid A} (n : N) (x : A) : A :=
  match n with
  | N0 => idn
  | Npos p => popr p x
  end.

Definition zopr {A : Type} `{is_group : IsGroup A} (n : Z) (x : A) : A :=
  match n with
  | Z0 => idn
  | Zpos p => popr p x
  | Zneg p => inv (popr p x)
  end.
