(** * Injectivity *)

From DEZ Require Export
  Init.

Class IsInjGen (A B C D : Type) (X : C -> D -> Prop) (S : A -> B -> Prop)
  (f : A -> C) (g : B -> D) : Prop :=
  inj_gen (x : A) (y : B) (a : X (f x) (g y)) : S x y.

(** ** Injective Function *)

Class IsInj (A B : Type) (X : B -> B -> Prop) (S : A -> A -> Prop)
  (f : A -> B) : Prop :=
  inj (x y : A) (a : X (f x) (f y)) : S x y.
