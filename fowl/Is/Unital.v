(** * Unitality *)

From DEZ Require Export
  Init.

(** ** Left-Unital Binary Function *)

Fail Fail Class IsUnlBinFnL (A B C : Type) (X : C -> C -> Prop)
  (x : A) (y : C) (k : A -> B -> C) : Prop :=
  unl_bin_fn_l (z : B) : X (k x z) y.

(** ** Right-Unital Binary Function *)

Fail Fail Class IsUnlBinFnR (A B C : Type) (X : C -> C -> Prop)
  (x : B) (y : C) (k : A -> B -> C) : Prop :=
  unl_bin_fn_r (z : A) : X (k z x) y.

(** ** Left-Unital Action *)

Class IsUnlActL (A B : Type) (X : B -> B -> Prop)
  (x : A) (al : A -> B -> B) : Prop :=
  unl_act_l (a : B) : X (al x a) a.

(** ** Right-Unital Action *)

Class IsUnlActR (A B : Type) (X : B -> B -> Prop)
  (x : A) (ar : B -> A -> B) : Prop :=
  unl_act_r (a : B) : X (ar a x) a.

(** ** Left-Unital Binary Operation *)

(** This has the same shape as [Z.add_0_l]. *)

Class IsUnlL (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  unl_l (y : A) : X (k x y) y.

(** ** Right-Unital Binary Operation *)

(** This has the same shape as [Z.add_0_r]. *)

Class IsUnlR (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  unl_r (y : A) : X (k y x) y.

(** ** Unital Binary Operation *)

Class IsUnl (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop := {
  unl_is_unl_l :> IsUnlL X x k;
  unl_is_unl_r :> IsUnlR X x k;
}.
