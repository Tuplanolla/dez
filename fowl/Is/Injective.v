(** * Injectivity *)

From DEZ Require Export
  Init.

Class IsInjGen (A B C D : Type) (X : C -> D -> Prop) (Y : A -> B -> Prop)
  (f : A -> C) (g : B -> D) : Prop :=
  inj_gen (x : A) (y : B) (a : X (f x) (g y)) : Y x y.

(** ** Injective Function *)

Class IsInj2 (A B : Type) (X : B -> B -> Prop) (Y : A -> A -> Prop)
  (f : A -> B) : Prop :=
  inj2 (x y : A) (a : X (f x) (f y)) : Y x y.

(** ** Injective Operation *)

Class IsInj (A : Type) (X : A -> A -> Prop) (f : A -> A) : Prop :=
  inj (x y : A) (a : X (f x) (f y)) : X x y.
