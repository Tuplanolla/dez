(** * Unitality *)

From DEZ Require Export
  Init.

(** ** Left Unital Binary Function *)

(** This has the same shape as [add_0_l]. *)

Class IsUnlL (A B C : Type) (R : C -> A -> Prop)
  (x : B) (k : B -> A -> C) : Prop :=
  unl_l (y : A) : R (k x y) y.

(** ** Right Unital Binary Function *)

(** This has the same shape as [add_0_r]. *)

Class IsUnlR (A B C : Type) (R : C -> A -> Prop)
  (x : B) (k : A -> B -> C) : Prop :=
  unl_r (y : A) : R (k y x) y.

(** ** Unital Binary Functions *)

Class IsUnlLR2 (A B C : Type) (R : C -> A -> Prop)
  (x : B) (k : B -> A -> C) (m : A -> B -> C) : Prop := {
  is_unl_l :> IsUnlL R x k;
  is_unl_r :> IsUnlR R x m;
}.

(** ** Unital Torsion *)

Class IsUnlLR (A B : Type) (R : A -> B -> Prop)
  (x : B) (k : B -> B -> A) : Prop :=
  is_unl_l_r_2 :> IsUnlLR2 R x k k.
