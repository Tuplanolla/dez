(** * Cancellativity *)

From DEZ.Is Require Export
  Injective.

(** ** Left-Cancellative Binary Function *)

Class IsCancelBinFnL (A0 A1 B : Type)
  (X : A0 -> A0 -> Prop) (Y : B -> B -> Prop)
  (k : A1 -> A0 -> B) : Prop :=
  cancel_bin_fn_l (x : A1) (y z : A0) (a : Y (k x y) (k x z)) : X y z.

Section Context.

Context (A0 A1 B : Type)
  (X : A0 -> A0 -> Prop) (Y : B -> B -> Prop)
  (k : A1 -> A0 -> B).

(** Left-cancellativity of a binary function
    is a special case of the injectivity of its partial application. *)

#[export] Instance cancel_bin_fn_l_is_inj_un_fn
  `{!IsCancelBinFnL X Y k} (x : A1) : IsInjUnFn X Y (k x).
Proof. intros y z. apply cancel_bin_fn_l. Qed.

#[local] Instance inj_un_fn_is_cancel_bin_fn_l
  `{!forall x : A1, IsInjUnFn X Y (k x)} : IsCancelBinFnL X Y k.
Proof. intros x y z. apply inj_un_fn. Qed.

End Context.

(** ** Right-Cancellative Binary Function *)

Class IsCancelBinFnR (A0 A1 B : Type)
  (X : A0 -> A0 -> Prop) (Y : B -> B -> Prop)
  (k : A0 -> A1 -> B) : Prop :=
  cancel_bin_fn_r (x y : A0) (z : A1) (a : Y (k x z) (k y z)) : X x y.

Section Context.

Context (A0 A1 B : Type)
  (X : A0 -> A0 -> Prop) (Y : B -> B -> Prop)
  (k : A0 -> A1 -> B).

(** Right-cancellativity of a binary function
    is a special case of the injectivity of its flipped partial application. *)

#[export] Instance cancel_bin_fn_r_is_inj_un_fn_flip
  `{!IsCancelBinFnR X Y k} (z : A1) : IsInjUnFn X Y (flip k z).
Proof. intros x y. unfold flip. apply cancel_bin_fn_r. Qed.

#[local] Instance inj_un_fn_flip_is_cancel_bin_fn_r
  `{!forall z : A1, IsInjUnFn X Y (flip k z)} : IsCancelBinFnR X Y k.
Proof.
  intros x y z.
  change (k x z) with (flip k z x). change (k y z) with (flip k z y).
  apply inj_un_fn. Qed.

End Context.

Section Context.

Context (A B C : Type) (X : B -> B -> Prop) (Y : C -> C -> Prop)
  (k : A -> B -> C).

(** Left-cancellativity of a binary function
    is a special case of the right-cancellativity of its flipped version. *)

#[local] Instance cancel_bin_fn_l_is_cancel_bin_fn_r_flip
  `{!IsCancelBinFnL X Y k} : IsCancelBinFnR X Y (flip k).
Proof. intros y z x a. unfold flip in *. eauto. Qed.

#[local] Instance cancel_bin_fn_r_flip_is_cancel_bin_fn_l
  `{!IsCancelBinFnR X Y (flip k)} : IsCancelBinFnL X Y k.
Proof. intros x y z a. unfold flip in *. eauto. Qed.

End Context.

(** ** Left-Cancellative Action *)
(** ** Left-Cancellative Left Action *)

Class IsCancelActL (A B : Type) (X : B -> B -> Prop)
  (al : A -> B -> B) : Prop :=
  cancel_act_l (x : A) (a b : B) (s : X (al x a) (al x b)) : X a b.

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (al : A -> B -> B).

(** Left-cancellativity of an action is a special case
    of the left-cancellativity of a binary function. *)

#[export] Instance cancel_act_l_is_cancel_bin_fn_l
  `{!IsCancelActL X al} : IsCancelBinFnL X X al.
Proof. auto. Qed.

#[local] Instance cancel_bin_fn_l_is_cancel_act_l
  `{!IsCancelBinFnL X X al} : IsCancelActL X al.
Proof. auto. Qed.

End Context.

(** ** Left-Cancellative Right Action *)

Class IsCancelActRL (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (ar : B -> A -> B) : Prop :=
  cancel_act_r_l (a : B) (x y : A) (s : Y (ar a x) (ar a y)) : X x y.

Section Context.

Context (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (ar : B -> A -> B).

(** Left-cancellativity of a right action is a special case
    of the left-cancellativity of a binary function. *)

#[export] Instance cancel_act_r_l_is_cancel_bin_fn_l
  `{!IsCancelActRL X Y ar} : IsCancelBinFnL X Y ar.
Proof. auto. Qed.

#[local] Instance cancel_bin_fn_l_is_cancel_act_r_l
  `{!IsCancelBinFnL X Y ar} : IsCancelActRL X Y ar.
Proof. auto. Qed.

End Context.

(** ** Right-Cancellative Left Action *)

Class IsCancelActLR (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (al : A -> B -> B) : Prop :=
  cancel_act_l_r (x y : A) (a : B) (s : Y (al x a) (al y a)) : X x y.

Section Context.

Context (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (al : A -> B -> B).

(** Right-cancellativity of a left action is a special case
    of the right-cancellativity of a binary function. *)

#[export] Instance cancel_act_l_r_is_cancel_bin_fn_r
  `{!IsCancelActLR X Y al} : IsCancelBinFnR X Y al.
Proof. auto. Qed.

#[local] Instance cancel_bin_fn_r_is_cancel_act_l_r
  `{!IsCancelBinFnR X Y al} : IsCancelActLR X Y al.
Proof. auto. Qed.

End Context.

(** ** Right-Cancellative Action *)
(** ** Right-Cancellative Right Action *)

Class IsCancelActR (A B : Type) (X : B -> B -> Prop)
  (ar : B -> A -> B) : Prop :=
  cancel_act_r (a b : B) (x : A) (s : X (ar a x) (ar b x)) : X a b.

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (ar : B -> A -> B).

(** Right-cancellativity of an action is a special case
    of the right-cancellativity of a binary function. *)

#[export] Instance cancel_act_r_is_cancel_bin_fn_r
  `{!IsCancelActR X ar} : IsCancelBinFnR X X ar.
Proof. auto. Qed.

#[local] Instance cancel_bin_fn_r_is_cancel_act_r
  `{!IsCancelBinFnR X X ar} : IsCancelActR X ar.
Proof. auto. Qed.

End Context.

(** ** Left-Cancellative Form *)

Class IsCancelFormL (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (s : B -> B -> A) : Prop :=
  cancel_form_l (a b c : B) (t : X (s a b) (s a c)) : Y b c.

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

End Context.

(** ** Right-Cancellative Form *)

Class IsCancelFormR (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (s : B -> B -> A) : Prop :=
  cancel_form_r (a b c : B) (t : X (s a c) (s b c)) : Y a b.

Section Context.

Context (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (s : B -> B -> A).

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

Section Context.

Context (A : Type) (X : A -> A -> Prop) (k : A -> A -> A).

(** Left-cancellativity of a binary operation is a special case
    of the left-cancellativity of a binary function. *)

#[export] Instance cancel_l_is_cancel_bin_fn_l
  `{!IsCancelL X k} : IsCancelBinFnL X X k.
Proof. auto. Qed.

#[local] Instance cancel_bin_fn_l_is_cancel_l
  `{!IsCancelBinFnL X X k} : IsCancelL X k.
Proof. auto. Qed.

End Context.

(** ** Right-Cancellative Binary Operation *)

(** This has the same shape as [Pos.add_reg_r]. *)

Class IsCancelR (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop :=
  cancel_r (x y z : A) (a : X (k x z) (k y z)) : X x y.

Section Context.

Context (A : Type) (X : A -> A -> Prop) (k : A -> A -> A).

(** Right-cancellativity of a binary operation is a special case
    of the right-cancellativity of a binary function. *)

#[export] Instance cancel_r_is_cancel_bin_fn_r
  `{!IsCancelR X k} : IsCancelBinFnR X X k.
Proof. auto. Qed.

#[local] Instance cancel_bin_fn_r_is_cancel_r
  `{!IsCancelBinFnR X X k} : IsCancelR X k.
Proof. auto. Qed.

End Context.

(** ** Cancellative Binary Operation *)
(** ** Injective Binary Operation *)
(** ** Regular Binary Operation *)

Class IsCancel (A : Type) (X : A -> A -> Prop) (k : A -> A -> A) : Prop := {
  cancel_is_cancel_l :> IsCancelL X k;
  cancel_is_cancel_r :> IsCancelR X k;
}.
