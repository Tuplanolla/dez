(** * Distributivity *)

From DEZ.Is Require Export
  Injective Proper.

(** ** Distributive Unary Functions over Binary Functions *)

Class IsDistrFns (A0 A1 B0 B1 B2 C : Type) (X : C -> C -> Prop)
  (f : A0 -> B0) (g : A1 -> B1) (k : A0 -> A1 -> B2)
  (h : B2 -> C) (m : B0 -> B1 -> C) : Prop :=
  distr_fns (x : A0) (y : A1) : X (h (k x y)) (m (f x) (g y)).

(** ** Distributive Unary Functions over Forms *)

Class IsDistrForms (A B C : Type) (X : A -> A -> Prop)
  (f : C -> B) (s : C -> C -> B) (g : B -> A) (t : B -> B -> A) : Prop :=
  distr_forms (a b : C) : X (g (s a b)) (t (f a) (f b)).

Section Context.

Context (A B C : Type) (X : A -> A -> Prop)
  (f : C -> B) (s : C -> C -> B) (g : B -> A) (t : B -> B -> A).

(** Something implies something else. *)

#[export] Instance distr_fns_is_distr_forms
  `{!IsDistrFns X f f s g t} : IsDistrForms X f s g t.
Proof. auto. Qed.

(** Something implies something else. *)

#[local] Instance distr_forms_is_distr_fns
  `{!IsDistrForms X f s g t} : IsDistrFns X f f s g t.
Proof. auto. Qed.

End Context.

(** ** Distributive Unary Operation over Binary Operation *)

(** This has the same shape as [Z.opp_add_distr]. *)

Class IsDistrUnOp (A : Type) (X : A -> A -> Prop)
  (f : A -> A) (k : A -> A -> A) : Prop :=
  distr_un_op (x y : A) : X (f (k x y)) (k (f x) (f y)).

(** ** Antidistributive Unary Operation over Binary Operation *)

Class IsAntidistrUnOp (A : Type) (X : A -> A -> Prop)
  (f : A -> A) (k : A -> A -> A) : Prop :=
  antidistr_un_op (x y : A) : X (f (k x y)) (k (f y) (f x)).

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (f : A -> A) (k : A -> A -> A).

(** Something implies something else. *)

#[export] Instance distr_forms_is_distr_un_op
  `{!IsDistrForms X f k f k} : IsDistrUnOp X f k.
Proof. auto. Qed.

(** Something implies something else. *)

#[local] Instance distr_un_op_is_distr_forms
  `{!IsDistrUnOp X f k} : IsDistrForms X f k f k.
Proof. auto. Qed.

(** Something implies something else. *)

#[export] Instance distr_forms_is_antidistr_un_op_flip
  `{!IsDistrForms X f (flip k) f k} : IsAntidistrUnOp X f (flip k).
Proof. auto. Qed.

(** Something implies something else. *)

#[local] Instance antidistr_un_op_is_distr_forms_flip
  `{!IsAntidistrUnOp X f k} : IsDistrForms X f k f (flip k).
Proof. auto. Qed.

End Context.

(** ** Left Distributive Action over Binary Operation *)

Class IsDistrActL (A B : Type) (X : B -> B -> Prop)
  (al : A -> B -> B) (k : B -> B -> B) : Prop :=
  distr_act_l (x : A) (a b : B) : X (al x (k a b)) (k (al x a) (al x b)).

(** ** Right Distributive Action over Binary Operation *)

Class IsDistrActR (A B : Type) (X : B -> B -> Prop)
  (ar : B -> A -> B) (k : B -> B -> B) : Prop :=
  distr_act_r (a b : B) (x : A) : X (ar (k a b) x) (k (ar a x) (ar b x)).

(** ** Left Distributive Binary Operation over Binary Operation *)

(** This has the same shape as [Z.mul_add_distr_l]. *)

Class IsDistrL (A : Type) (X : A -> A -> Prop) (k m : A -> A -> A) : Prop :=
  distr_l (x y z : A) : X (k x (m y z)) (m (k x y) (k x z)).

(** ** Right Distributive Binary Operation over Binary Operation *)

(** This has the same shape as [Z.mul_add_distr_r]. *)

Class IsDistrR (A : Type) (X : A -> A -> Prop) (k m : A -> A -> A) : Prop :=
  distr_r (x y z : A) : X (k (m x y) z) (m (k x z) (k y z)).

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) (m : A -> A -> A).

(** Left distributive form implies left distributive binary operation. *)

#[export] Instance distr_act_l_is_distr_l
  `{!IsDistrActL X k m} : IsDistrL X k m.
Proof. auto. Qed.

(** Left distributive binary operation implies left distributive form. *)

#[local] Instance distr_l_is_distr_act_l
  `{!IsDistrL X k m} : IsDistrActL X k m.
Proof. auto. Qed.

(** Right distributive form implies right distributive binary operation. *)

#[export] Instance distr_act_r_is_distr_r
  `{!IsDistrActR X k m} : IsDistrR X k m.
Proof. auto. Qed.

(** Right distributive binary operation implies right distributive form. *)

#[local] Instance distr_r_is_distr_act_r
  `{!IsDistrR X k m} : IsDistrActR X k m.
Proof. auto. Qed.

End Context.

(** ** Distributive Binary Operation over Binary Operation *)

Class IsDistr (A : Type) (X : A -> A -> Prop) (k m : A -> A -> A) : Prop := {
  distr_is_distr_l :> IsDistrL X k m;
  distr_is_distr_r :> IsDistrR X k m;
}.

Section Context.

Context (A B : Type) (X : B -> B -> Prop) (al : A -> B -> B) (k : B -> B -> B).

(** Left distributivity implies distributivity of partial applications. *)

#[export] Instance distr_act_l_is_distr_un_op
  `{!IsDistrActL X al k} (x : A) : IsDistrUnOp X (al x) k.
Proof. intros a b. apply distr_act_l. Qed.

(** Same in reverse. *)

#[local] Instance distr_un_op_is_distr_act_l
  `{!forall x : A, IsDistrUnOp X (al x) k} : IsDistrActL X al k.
Proof. intros x a b. apply distr_un_op. Qed.

End Context.

Section Context.

Context (A B : Type) (X : B -> B -> Prop) (ar : B -> A -> B) (k : B -> B -> B).

(** Right distributivity implies distributivity of partial applications. *)

#[export] Instance distr_act_r_is_distr_un_op
  `{!IsDistrActR X ar k} (x : A) : IsDistrUnOp X (flip ar x) k.
Proof. intros a b. apply (distr_act_r (ar := ar)). Qed.

(** Same in reverse. *)

#[local] Instance distr_un_op_is_distr_act_r
  `{!forall x : A, IsDistrUnOp X (flip ar x) k} : IsDistrActR X ar k.
Proof. intros a b x. apply (distr_un_op (f := flip ar x)). Qed.

End Context.

Section Context.

Context (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop) (f : A -> B).

(** Properness is a special case of distributivity. *)

#[local] Instance distr_fns_is_proper
  `{!IsDistrFns impl f f X id Y} : IsProper (X ==> Y) f.
Proof. auto. Qed.

(** Injectivity is a special case of distributivity. *)

#[local] Instance distr_fns_is_inj_fn
  `{!IsDistrFns (flip impl) f f X id Y} : IsInjFn X Y f.
Proof. auto. Qed.

End Context.
