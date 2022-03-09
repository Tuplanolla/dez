(** * Cancellativity *)

From DEZ.Is Require Export
  Injective.

(** ** Left-Cancellative Binary Function *)

Class IsCancelBinFnL (A B C : Type) (X : B -> B -> Prop) (Y : C -> C -> Prop)
  (k : A -> B -> C) : Prop :=
  cancel_bin_fn_l (x : A) (y z : B) (a : Y (k x y) (k x z)) : X y z.

Section Context.

Context (A B C : Type) (X : B -> B -> Prop) (Y : C -> C -> Prop)
  (k : A -> B -> C).

(** Injectivity of a partially-applied binary function
    is left-cancellativity. *)

#[export] Instance cancel_bin_fn_l_is_inj_un_fn
  `{!IsCancelBinFnL X Y k} (x : A) : IsInjUnFn X Y (k x).
Proof. intros y z. apply cancel_bin_fn_l. Qed.

#[local] Instance inj_un_fn_is_cancel_bin_fn_l
  `{!forall x : A, IsInjUnFn X Y (k x)} : IsCancelBinFnL X Y k.
Proof. intros x y z. apply inj_un_fn. Qed.

End Context.

(** ** Right-Cancellative Binary Function *)

Class IsCancelBinFnR (A B C : Type) (X : A -> A -> Prop) (Y : C -> C -> Prop)
  (k : A -> B -> C) : Prop :=
  cancel_bin_fn_r (x y : A) (z : B) (a : Y (k x z) (k y z)) : X x y.

Section Context.

Context (A B C : Type) (X : A -> A -> Prop) (Y : C -> C -> Prop)
  (k : A -> B -> C).

(** Injectivity of a partially-applied flipped binary function
    is right-cancellativity. *)

#[export] Instance cancel_bin_fn_r_is_inj_un_fn_flip
  `{!IsCancelBinFnR X Y k} (z : B) : IsInjUnFn X Y (flip k z).
Proof. intros x y. unfold flip. apply cancel_bin_fn_r. Qed.

#[local] Instance inj_un_fn_flip_is_cancel_bin_fn_r
  `{!forall y : B, IsInjUnFn X Y (flip k y)} : IsCancelBinFnR X Y k.
Proof.
  intros x y z.
  change (k x z) with (flip k z x). change (k y z) with (flip k z y).
  apply inj_un_fn. Qed.

End Context.

Section Context.

Context (A B C : Type) (X : B -> B -> Prop) (Y : C -> C -> Prop)
  (k : A -> B -> C).

(** Right-cancellativity of a flipped binary function
    is left-cancellativity. *)

#[export] Instance cancel_bin_fn_l_is_cancel_bin_fn_r_flip
  `{!IsCancelBinFnL X Y k} : IsCancelBinFnR X Y (flip k).
Proof. intros x y z. unfold flip. apply (cancel_bin_fn_l (k := k)). Qed.

#[local] Instance cancel_bin_fn_r_flip_is_cancel_bin_fn_l
  `{!IsCancelBinFnR X Y (flip k)} : IsCancelBinFnL X Y k.
Proof.
  intros x y z.
  change (k x y) with (flip k y x). change (k x z) with (flip k z x).
  apply cancel_bin_fn_r. Qed.

End Context.

(** ** Left-Cancellative Form *)

Class IsCancelFormL (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (s : B -> B -> A) : Prop :=
  cancel_form_l (a b c : B) (t : X (s a b) (s a c)) : Y b c.

(** ** Right-Cancellative Form *)

Class IsCancelFormR (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (s : B -> B -> A) : Prop :=
  cancel_form_r (a b c : B) (t : X (s a c) (s b c)) : Y a b.

Section Context.

Context (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (s : B -> B -> A).

(** Left-cancellativity of a form is a special case
    of the left-cancellativity of a binary function. *)

#[export] Instance cancel_form_l_is_cancel_bin_fn_l
  `{!IsCancelFormL X Y s} : IsCancelBinFnL Y X s.
Proof. auto. Qed.

#[local] Instance cancel_bin_fn_l_is_cancel_form_l
  `{!IsCancelBinFnL Y X s} : IsCancelFormL X Y s.
Proof. auto. Qed.

(** Right-cancellativity of a form is a special case
    of the right-cancellativity of a binary function. *)

#[export] Instance cancel_form_r_is_cancel_bin_fn_r
  `{!IsCancelFormR X Y s} : IsCancelBinFnR Y X s.
Proof. auto. Qed.

#[local] Instance cancel_bin_fn_r_is_cancel_form_r
  `{!IsCancelBinFnR Y X s} : IsCancelFormR X Y s.
Proof. auto. Qed.

End Context.

(** ** Cancellative Form *)

Class IsCancelForm (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (s : B -> B -> A) : Prop := {
  cancel_form_is_cancel_form_l :> IsCancelFormL X Y s;
  cancel_form_is_cancel_form_r :> IsCancelFormR X Y s;
}.

(** ** Left-Cancellative Binary Operation *)

(** This has the same shape as [Pos.add_reg_l]. *)

Class IsCancelL (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  cancel_l (x y z : A) (a : X (k x y) (k x z)) : X y z.

(** ** Right-Cancellative Binary Operation *)

(** This has the same shape as [Pos.add_reg_r]. *)

Class IsCancelR (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  cancel_r (x y z : A) (a : X (k x z) (k y z)) : X x y.

(** ** Cancellative Binary Operation *)
(** ** Injective Binary Operation *)
(** ** Regular Binary Operation *)

Class IsCancel (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop := {
  cancel_is_cancel_l :> IsCancelL X k;
  cancel_is_cancel_r :> IsCancelR X k;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop) (k : A -> A -> A).

(** Left-cancellativity of a binary operation is a special case
    of the left-cancellativity of a form. *)

Lemma cancel_l_is_cancel_form_l
  `{!IsCancelL X k} : IsCancelFormL X X k.
Proof. auto. Qed.

Lemma cancel_form_l_is_cancel_l
  `{!IsCancelFormL X X k} : IsCancelL X k.
Proof. auto. Qed.

(** Right-cancellativity of a binary operation is a special case
    of the right-cancellativity of a form. *)

Lemma cancel_r_is_cancel_form_r
  `{!IsCancelR X k} : IsCancelFormR X X k.
Proof. auto. Qed.

Lemma cancel_form_r_is_cancel_r
  `{!IsCancelFormR X X k} : IsCancelR X k.
Proof. auto. Qed.

(** Cancellativity of a binary operation is a special case
    of the cancellativity of a form. *)

#[export] Instance cancel_is_cancel_form
  `{!IsCancel X k} : IsCancelForm X X k.
Proof.
  esplit; eauto
  using cancel_l_is_cancel_form_l, cancel_r_is_cancel_form_r
  with typeclass_instances. Qed.

#[local] Instance cancel_form_is_cancel
  `{!IsCancelForm X X k} : IsCancel X k.
Proof.
  esplit; eauto
  using cancel_form_l_is_cancel_l, cancel_form_r_is_cancel_r
  with typeclass_instances. Qed.

#[export] Existing Instance cancel_l_is_cancel_form_l.
#[local] Existing Instance cancel_form_l_is_cancel_l.
#[export] Existing Instance cancel_r_is_cancel_form_r.
#[local] Existing Instance cancel_form_r_is_cancel_r.

End Context.
