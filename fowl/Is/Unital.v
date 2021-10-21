(** * Unitality *)

From DEZ Require Export
  Init.

(** ** Left Unital Binary Function *)

(** This has the same shape as [add_0_l]. *)

Class IsUnlL (A B C : Type) (X : C -> A -> Prop)
  (x : B) (k : B -> A -> C) : Prop :=
  unl_l (y : A) : X (k x y) y.

(** ** Right Unital Binary Function *)

(** This has the same shape as [add_0_r]. *)

Class IsUnlR (A B C : Type) (X : C -> A -> Prop)
  (x : B) (k : A -> B -> C) : Prop :=
  unl_r (y : A) : X (k y x) y.

(** ** Unital Binary Functions *)

Class IsUnlLR2 (A B C : Type) (X : C -> A -> Prop)
  (x : B) (k : B -> A -> C) (m : A -> B -> C) : Prop := {
  is_unl_l :> IsUnlL X x k;
  is_unl_r :> IsUnlR X x m;
}.

(** ** Unital Torsion *)

Class IsUnlLR (A B : Type) (X : A -> B -> Prop)
  (x : B) (k : B -> B -> A) : Prop :=
  is_unl_l_r_2 :> IsUnlLR2 X x k k.
