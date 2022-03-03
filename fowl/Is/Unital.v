(** * Unitality *)

From DEZ Require Export
  Init.

(** ** Left Unital Action *)

Class IsUnlActL (A B : Type) (X : B -> B -> Prop)
  (x : A) (al : A -> B -> B) : Prop :=
  unl_act_l (a : B) : X (al x a) a.

(** ** Right Unital Action *)

Class IsUnlActR (A B : Type) (X : B -> B -> Prop)
  (x : A) (ar : B -> A -> B) : Prop :=
  unl_act_r (a : B) : X (ar a x) a.

(** ** Left Unital Binary Operation *)

(** This has the same shape as [Z.add_0_l]. *)

Class IsUnlL (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  unl_l (y : A) : X (k x y) y.

(** ** Right Unital Binary Operation *)

(** This has the same shape as [Z.add_0_r]. *)

Class IsUnlR (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  unl_r (y : A) : X (k y x) y.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A).

(** Left unital action implies left unital binary operation. *)

#[export] Instance unl_act_l_is_unl_l
  `{!IsUnlActL X x k} : IsUnlL X x k.
Proof. auto. Qed.

(** Left unital binary operation implies left unital action. *)

#[local] Instance unl_l_is_unl_act_l
  `{!IsUnlL X x k} : IsUnlActL X x k.
Proof. auto. Qed.

(** Right unital action implies right unital binary operation. *)

#[export] Instance unl_act_r_is_unl_r
  `{!IsUnlActR X x k} : IsUnlR X x k.
Proof. auto. Qed.

(** Right unital binary operation implies right unital action. *)

#[local] Instance unl_r_is_unl_act_r
  `{!IsUnlR X x k} : IsUnlActR X x k.
Proof. auto. Qed.

End Context.

(** ** Unital Binary Operation *)

Class IsUnl (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop := {
  unl_is_unl_l :> IsUnlL X x k;
  unl_is_unl_r :> IsUnlR X x k;
}.
