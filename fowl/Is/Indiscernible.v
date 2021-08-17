(** * Identity of Indiscernibles *)

From DEZ.Has Require Export
  NullaryOperation Distance.
From DEZ.ShouldHave Require Import
  AdditiveNotations.

(* R (S (d y z) x) (S x y) *)

Class IsIndisc (A B : Type) (Hx : HasNullOp A) (Hd : HasDist A B) : Prop :=
  indisc (x y : B) : dist x y = 0 <-> x = y.
