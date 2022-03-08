(** * Cancellativity *)

From DEZ.Is Require Export
  Injective.

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

Section Context.

Context (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (s : A -> A -> B).

(** Something implies something else. *)

#[export] Instance cancel_form_l_is_cancel_form_r_flip
  `{!IsCancelFormL X Y s} : IsCancelFormR X Y (flip s).
Proof. intros x y z. unfold flip. apply cancel_form_l. Qed.

(** Something implies something else. *)

#[local] Instance cancel_form_r_is_cancel_form_l_flip
  `{!IsCancelFormR X Y s} : IsCancelFormL X Y (flip s).
Proof. intros x y z. unfold flip. apply cancel_form_r. Qed.

End Context.

Section Context.

Context (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (s : A -> A -> B).

(** Left cancellativity implies injectivity of partial applications. *)

#[export] Instance cancel_form_l_is_inj_fn
  `{!IsCancelFormL X Y s} (a : A) : IsInjFn X Y (s a).
Proof. intros x y. apply cancel_form_l. Qed.

(** Injectivity of partial applications implies left cancellativity. *)

#[local] Instance inj_fn_is_cancel_form_l
  `{!forall a : A, IsInjFn X Y (s a)} : IsCancelFormL X Y s.
Proof. intros x y a. apply inj_fn. Qed.

(** Right cancellativity implies injectivity of partial applications. *)

#[export] Instance cancel_form_r_is_inj_fn
  `{!IsCancelFormR X Y s} (a : A) : IsInjFn X Y (flip s a).
Proof. intros x y. apply (cancel_form_r (s := s)). Qed.

(** Injectivity of partial applications implies right cancellativity. *)

#[local] Instance inj_fn_is_cancel_form_r
  `{!forall a : A, IsInjFn X Y (flip s a)} : IsCancelFormR X Y s.
Proof. intros x y a. apply (inj_fn (f := flip s a)). Qed.

End Context.

(** ** Left Cancellative Binary Operation with Excluded Point *)

(** This has the same shape as [Z.mul_reg_l]. *)

Class IsExCancelL (A : Type) (X : A -> A -> Prop) (Y : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  ex_cancel_l (y z w : A) (a : Y w x) (a : X (k w y) (k w z)) : X y z.

(** ** Right Cancellative Binary Operation with Excluded Point *)

(** This has the same shape as [Z.mul_reg_r]. *)

Class IsExCancelR (A : Type) (X : A -> A -> Prop) (Y : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop :=
  ex_cancel_r (y z w : A) (a : Y w x) (b : X (k y w) (k z w)) : X y z.

(** ** Cancellative Binary Operation with Excluded Point *)

Class IsExCancel (A : Type) (X : A -> A -> Prop) (Y : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop := {
  ex_cancel_is_ex_cancel_l :> IsExCancelL X Y x k;
  ex_cancel_is_ex_cancel_r :> IsExCancelR X Y x k;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop) (Y : A -> A -> Prop)
  (x : A) (k : A -> A -> A).

(** Left cancellative binary operation
    implies left cancellative binary operation with excluded point. *)

#[export] Instance cancel_l_is_ex_cancel_l
  `{!IsCancelL X k} : IsExCancelL X Y x k.
Proof. intros y z w a b. eauto. Qed.

(** Right cancellative binary operation
    implies right cancellative binary operation with excluded point. *)

#[export] Instance cancel_r_is_ex_cancel_r
  `{!IsCancelR X k} : IsExCancelR X Y x k.
Proof. intros y z w a b. eauto. Qed.

(** Cancellative binary operation
    implies cancellative binary operation with excluded point. *)

#[export] Instance cancel_is_ex_cancel
  `{!IsCancel X k} : IsExCancel X Y x k.
Proof. esplit; typeclasses eauto. Qed.

End Context.
