(** * Invertibility *)

From DEZ Require Export
  Init.

(** ** Left Invertible Binary Function *)

Class IsInvBinFnL (A B C : Type) (X : C -> C -> Prop)
  (x : C) (f : A -> B) (k : B -> A -> C) : Prop :=
  inv_bin_fn_l (y : A) : X (k (f y) y) x.

(** ** Right Invertible Binary Function *)

Class IsInvBinFnR (A B C : Type) (X : C -> C -> Prop)
  (x : C) (f : A -> B) (k : A -> B -> C) : Prop :=
  inv_bin_fn_r (y : A) : X (k y (f y)) x.

(** ** Left Invertible Form *)

Class IsInvFormL (A B : Type) (X : B -> B -> Prop)
  (x : B) (f : A -> A) (s : A -> A -> B) : Prop :=
  inv_form_l (y : A) : X (s (f y) y) x.

(** ** Right Invertible Form *)

Class IsInvFormR (A B : Type) (X : B -> B -> Prop)
  (x : B) (f : A -> A) (s : A -> A -> B) : Prop :=
  inv_form_r (y : A) : X (s y (f y)) x.

(** ** Invertible Form *)

Class IsInvForm (A B : Type) (X : B -> B -> Prop)
  (x : B) (f : A -> A) (s : A -> A -> B) : Prop := {
  inv_form_is_inv_form_l :> IsInvFormL X x f s;
  inv_form_is_inv_form_r :> IsInvFormR X x f s;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (s : A -> A -> A).

(** Left invertible binary function implies left invertible form. *)

#[export] Instance inv_bin_fn_l_is_inv_form_l
  `{!IsInvBinFnL X x f s} : IsInvFormL X x f s.
Proof. auto. Qed.

(** Left invertible form implies left invertible binary function. *)

#[local] Instance inv_form_l_is_inv_bin_fn_l
  `{!IsInvFormL X x f s} : IsInvBinFnL X x f s.
Proof. auto. Qed.

(** Right invertible binary function implies right invertible form. *)

#[export] Instance inv_bin_fn_r_is_inv_form_r
  `{!IsInvBinFnR X x f s} : IsInvFormR X x f s.
Proof. auto. Qed.

(** Right invertible form implies right invertible binary function. *)

#[local] Instance inv_form_r_is_inv_bin_fn_r
  `{!IsInvFormR X x f s} : IsInvBinFnR X x f s.
Proof. auto. Qed.

End Context.

(** ** Left Invertible Binary Operation *)

(** This has the same shape as [Z.add_opp_diag_l]. *)

Class IsInvL (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) : Prop :=
  inv_l (y : A) : X (k (f y) y) x.

(** ** Right Invertible Binary Operation *)

(** This has the same shape as [Z.add_opp_diag_r]. *)

Class IsInvR (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) : Prop :=
  inv_r (y : A) : X (k y (f y)) x.

(** ** Invertible Binary Operation *)

Class IsInv (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) : Prop := {
  inv_is_inv_l :> IsInvL X x f k;
  inv_is_inv_r :> IsInvR X x f k;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A).

(** We cannot declare these definitions to be instances
    until the end of this section if we want to avoid cycles. *)

(** Left invertible form implies left invertible binary operation. *)

Lemma inv_form_l_is_inv_l
  `{!IsInvFormL X x f k} : IsInvL X x f k.
Proof. auto. Qed.

(** Left invertible binary operation implies left invertible form. *)

Lemma inv_l_is_inv_form_l
  `{!IsInvL X x f k} : IsInvFormL X x f k.
Proof. auto. Qed.

(** Right invertible form implies right invertible binary operation. *)

Lemma inv_form_r_is_inv_r
  `{!IsInvFormR X x f k} : IsInvR X x f k.
Proof. auto. Qed.

(** Right invertible binary operation implies right invertible form. *)

Lemma inv_r_is_inv_form_r
  `{!IsInvR X x f k} : IsInvFormR X x f k.
Proof. auto. Qed.

(** Invertible form implies invertible binary operation. *)

#[export] Instance inv_form_is_inv
  `{!IsInvForm X x f k} : IsInv X x f k.
Proof.
  esplit; eauto
  using inv_form_l_is_inv_l, inv_form_r_is_inv_r
  with typeclass_instances. Qed.

(** Invertible binary operation implies invertible form. *)

#[local] Instance inv_is_inv_form
  `{!IsInv X x f k} : IsInvForm X x f k.
Proof.
  esplit; eauto
  using inv_l_is_inv_form_l, inv_r_is_inv_form_r
  with typeclass_instances. Qed.

#[export] Existing Instance inv_form_l_is_inv_l.
#[local] Existing Instance inv_l_is_inv_form_l.
#[export] Existing Instance inv_form_r_is_inv_r.
#[local] Existing Instance inv_r_is_inv_form_r.

End Context.
