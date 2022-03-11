(** * Invertibility *)

From DEZ Require Export
  Init.

(** ** Left-Invertible Binary Function *)

Class IsInvBinFnL (A B C : Type) (X : C -> C -> Prop)
  (x : C) (f : A -> B) (k : B -> A -> C) : Prop :=
  inv_bin_fn_l (y : A) : X (k (f y) y) x.

(** ** Right-Invertible Binary Function *)

Class IsInvBinFnR (A B C : Type) (X : C -> C -> Prop)
  (x : C) (f : A -> B) (k : A -> B -> C) : Prop :=
  inv_bin_fn_r (y : A) : X (k y (f y)) x.

(** ** Left-Invertible Form *)

Class IsInvFormL (A B : Type) (X : B -> B -> Prop)
  (x : B) (f : A -> A) (s : A -> A -> B) : Prop :=
  inv_form_l (y : A) : X (s (f y) y) x.

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (x : B) (f : A -> A) (s : A -> A -> B).

(** Left-invertibility of a form is a special case
    of the left-invertibility of a binary function. *)

#[export] Instance inv_form_l_is_inv_bin_fn_l
  `{!IsInvFormL X x f s} : IsInvBinFnL X x f s.
Proof. auto. Qed.

#[local] Instance inv_bin_fn_l_is_inv_form_l
  `{!IsInvBinFnL X x f s} : IsInvFormL X x f s.
Proof. auto. Qed.

End Context.

(** ** Right-Invertible Form *)

Class IsInvFormR (A B : Type) (X : B -> B -> Prop)
  (x : B) (f : A -> A) (s : A -> A -> B) : Prop :=
  inv_form_r (y : A) : X (s y (f y)) x.

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (x : B) (f : A -> A) (s : A -> A -> B).

(** Right-invertibility of a form is a special case
    of the right-invertibility of a binary function. *)

#[export] Instance inv_form_r_is_inv_bin_fn_r
  `{!IsInvFormR X x f s} : IsInvBinFnR X x f s.
Proof. auto. Qed.

#[local] Instance inv_bin_fn_r_is_inv_form_r
  `{!IsInvBinFnR X x f s} : IsInvFormR X x f s.
Proof. auto. Qed.

End Context.

(** ** Invertible Form *)

Class IsInvForm (A B : Type) (X : B -> B -> Prop)
  (x : B) (f : A -> A) (s : A -> A -> B) : Prop := {
  inv_form_is_inv_form_l :> IsInvFormL X x f s;
  inv_form_is_inv_form_r :> IsInvFormR X x f s;
}.

(** ** Left-Invertible Binary Operation *)

(** This has the same shape as [Z.add_opp_diag_l]. *)

Class IsInvL (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) : Prop :=
  inv_l (y : A) : X (k (f y) y) x.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A).

(** Left-invertibility of a binary operation is a special case
    of the left-invertibility of a binary function. *)

#[export] Instance inv_l_is_inv_bin_fn_l
  `{!IsInvL X x f k} : IsInvBinFnL X x f k.
Proof. auto. Qed.

#[local] Instance inv_bin_fn_l_is_inv_l
  `{!IsInvBinFnL X x f k} : IsInvL X x f k.
Proof. auto. Qed.

End Context.

(** ** Right-Invertible Binary Operation *)

(** This has the same shape as [Z.add_opp_diag_r]. *)

Class IsInvR (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) : Prop :=
  inv_r (y : A) : X (k y (f y)) x.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A).

(** Right-invertibility of a binary operation is a special case
    of the right-invertibility of a binary function. *)

#[export] Instance inv_r_is_inv_bin_fn_r
  `{!IsInvR X x f k} : IsInvBinFnR X x f k.
Proof. auto. Qed.

#[local] Instance inv_bin_fn_r_is_inv_r
  `{!IsInvBinFnR X x f k} : IsInvR X x f k.
Proof. auto. Qed.

End Context.

(** ** Invertible Binary Operation *)

Class IsInv (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) : Prop := {
  inv_is_inv_l :> IsInvL X x f k;
  inv_is_inv_r :> IsInvR X x f k;
}.
