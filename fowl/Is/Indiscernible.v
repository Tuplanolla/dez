(** * Identity of Indiscernibles *)

From Maniunfold.Has Require Export
  NullaryOperation Distance.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Class IsIndisc (A B : Type) (Hx : HasNullOp A) (Hd : HasDist A B) : Prop :=
  indisc (x y : B) : dist x y = 0 <-> x = y.
