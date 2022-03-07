(** * Injectivity and Cancellativity *)

From DEZ Require Export
  Init.

(** ** Injective Function *)

Class IsInjFn (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop :=
  inj_fn (x y : A) (a : Y (f x) (f y)) : X x y.

(** ** Cancellative Unary Operation *)
(** ** Injective Unary Operation *)

Class IsInj (A : Type) (X : A -> A -> Prop) (f : A -> A) : Prop :=
  inj (x y : A) (a : X (f x) (f y)) : X x y.

Section Context.

Context (A : Type) (X : A -> A -> Prop) (f : A -> A).

(** Injectivity of a function implies its injectivity as a binary operation. *)

#[export] Instance inj_fn_is_inj
  `{!IsInjFn X X f} : IsInj X f.
Proof. auto. Qed.

(** Injectivity of a binary operation implies its injectivity as a function. *)

#[local] Instance inj_is_inj_fn
  `{!IsInj X f} : IsInjFn X X f.
Proof. auto. Qed.

End Context.

(** ** Left Cancellative Form *)
(** ** Left Injective Form *)

Class IsCancelFormL (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (s : A -> A -> B) : Prop :=
  cancel_form_l (x y z : A) (a : Y (s x y) (s x z)) : X y z.

(** ** Left Cancellative Form *)
(** ** Left Injective Form *)

Class IsCancelFormR (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (s : A -> A -> B) : Prop :=
  cancel_form_r (x y z : A) (a : Y (s x z) (s y z)) : X x y.

(** ** Cancellative Form *)

Class IsCancelForm (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (s : A -> A -> B) : Prop := {
  cancel_form_is_cancel_form_l :> IsCancelFormL X Y s;
  cancel_form_is_cancel_form_r :> IsCancelFormR X Y s;
}.

(** ** Left Cancellative Binary Operation *)
(** ** Left Injective Binary Operation *)

(** This has the same shape as [Pos.add_reg_l]. *)

Class IsCancelL (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  cancel_l (x y z : A) (a : X (k x y) (k x z)) : X y z.

(** ** Right Cancellative Binary Operation *)
(** ** Right Injective Binary Operation *)

(** This has the same shape as [Pos.add_reg_r]. *)

Class IsCancelR (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  cancel_r (x y z : A) (a : X (k x z) (k y z)) : X x y.

(** ** Cancellative Binary Operation *)

Class IsCancel (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop := {
  cancel_is_cancel_l :> IsCancelL X k;
  cancel_is_cancel_r :> IsCancelR X k;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop) (k : A -> A -> A).

(** We cannot declare these definitions to be instances
    until the end of this section if we want to avoid cycles. *)

(** Left cancellative form implies left cancellative binary operation. *)

Lemma cancel_form_l_is_cancel_l
  `{!IsCancelFormL X X k} : IsCancelL X k.
Proof. auto. Qed.

(** Left cancellative binary operation implies left cancellative form. *)

Lemma cancel_l_is_cancel_form_l
  `{!IsCancelL X k} : IsCancelFormL X X k.
Proof. auto. Qed.

(** Right cancellative form implies right cancellative binary operation. *)

Lemma cancel_form_r_is_cancel_r
  `{!IsCancelFormR X X k} : IsCancelR X k.
Proof. auto. Qed.

(** Right cancellative binary operation implies right cancellative form. *)

Lemma cancel_r_is_cancel_form_r
  `{!IsCancelR X k} : IsCancelFormR X X k.
Proof. auto. Qed.

(** Cancellative form implies cancellative binary operation. *)

#[export] Instance cancel_form_is_cancel
  `{!IsCancelForm X X k} : IsCancel X k.
Proof.
  esplit; eauto
  using cancel_form_l_is_cancel_l, cancel_form_r_is_cancel_r
  with typeclass_instances. Qed.

(** Cancellative binary operation implies cancellative form. *)

#[local] Instance cancel_is_cancel_form
  `{!IsCancel X k} : IsCancelForm X X k.
Proof.
  esplit; eauto
  using cancel_l_is_cancel_form_l, cancel_r_is_cancel_form_r
  with typeclass_instances. Qed.

#[export] Existing Instance cancel_form_l_is_cancel_l.
#[local] Existing Instance cancel_l_is_cancel_form_l.
#[export] Existing Instance cancel_form_r_is_cancel_r.
#[local] Existing Instance cancel_r_is_cancel_form_r.

End Context.
