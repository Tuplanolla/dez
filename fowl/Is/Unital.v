(** * Unitality *)

From DEZ Require Export
  Init.

(** ** Unital Left Action *)

(** This has the same shape as [add_0_l]. *)

Class IsUnlL (A B : Type) (x : A) (k : A -> B -> B) : Prop :=
  unl_l (y : B) : k x y = y.

(** ** Unital Right Action *)

(** This has the same shape as [add_0_r]. *)

Class IsUnlR (A B : Type) (x : A) (k : B -> A -> B) : Prop :=
  unl_r (y : B) : k y x = y.

(** ** Unital Actions *)

Class IsUnlLR2 (A B : Type)
  (x : A) (k : A -> B -> B) (m : B -> A -> B) : Prop := {
  is_unl_l :> IsUnlL x k;
  is_unl_r :> IsUnlR x m;
}.

(** ** Unital Binary Operation *)

Class IsUnlLR (A : Type) (x : A) (k : A -> A -> A) : Prop :=
  is_unl_l_r_2 :> IsUnlLR2 x k k.
