(** * Distributivity and Preservation *)

From DEZ Require Export
  Init.

(** ** Distributive Unary Functions over Binary Functions *)

(** This unifies [IsDistrForms], [IsCommL] and many others. *)

Class IsDistrFns (A0 A1 B0 B1 B2 C : Type) (X : C -> C -> Prop)
  (f : A0 -> B0) (g : A1 -> B1) (k : A0 -> A1 -> B2)
  (h : B2 -> C) (m : B0 -> B1 -> C) : Prop :=
  distr_fns (x : A0) (y : A1) : X (h (k x y)) (m (f x) (g y)).

(** ** Distributive Unary Functions over Forms *)

Class IsDistrForms (A B C : Type) (X : C -> C -> Prop)
  (f : A -> B) (k : A -> A -> B) (g : B -> C) (m : B -> B -> C) : Prop :=
  distr_forms (x y : A) : X (g (k x y)) (m (f x) (f y)).

Section Context.

Context (A B C : Type) (X : C -> C -> Prop)
  (f : A -> B) (k : A -> A -> B) (g : B -> C) (m : B -> B -> C).

(** Something implies something else. *)

#[export] Instance distr_fns_is_distr_forms
  `{!IsDistrFns X f f k g m} : IsDistrForms X f k g m.
Proof. auto. Qed.

(** Something implies something else. *)

#[local] Instance distr_forms_is_distr_fns
  `{!IsDistrForms X f k g m} : IsDistrFns X f f k g m.
Proof. auto. Qed.

End Context.

(** ** Distributive Unary Operation over Binary Operation *)

(** This has the same shape as [Z.opp_add_distr]. *)

Class IsDistrUnOp (A : Type) (X : A -> A -> Prop)
  (f : A -> A) (k : A -> A -> A) : Prop :=
  distr_un_op (x y : A) : X (f (k x y)) (k (f x) (f y)).

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

Class IsDistrL (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) (m : A -> A -> A) : Prop :=
  distr_l (x y z : A) : X (k x (m y z)) (m (k x y) (k x z)).

(** ** Right Distributive Binary Operation over Binary Operation *)

(** This has the same shape as [Z.mul_add_distr_r]. *)

Class IsDistrR (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) (m : A -> A -> A) : Prop :=
  distr_r (x y z : A) : X (k (m x y) z) (m (k x z) (k y z)).

(** ** Distributive Binary Operation over Binary Operation *)

Class IsDistr (A : Type) (X : A -> A -> Prop)
  (k : A -> A -> A) (m : A -> A -> A) : Prop := {
  distr_is_distr_l :> IsDistrL X k m;
  distr_is_distr_r :> IsDistrR X k m;
}.

(** TODO These variants are missing. *)

(** ** Antidistributive Unary Operation over Binary Operation *)

Class IsAntidistr (A : Type) (X : A -> A -> Prop)
  (f : A -> A) (k : A -> A -> A) : Prop :=
  antidistr (x y : A) : X (f (k x y)) (k (f y) (f x)).

(** TODO These should be proofs. *)

Class Proper' (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f g : A -> B) : Prop :=
  is_distr_7'' :> IsDistrFns impl f g X id Y.

Eval cbv [Proper' IsDistrFns id impl] in Proper' ?[X] ?[Y] ?[f] ?[g].

Class IsInj' (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop :=
  is_distr_7' :> IsDistrFns (flip impl) f f X id Y.

Eval cbv [IsInj' IsDistrFns id flip impl] in IsInj' ?[X] ?[Y] ?[f].

(** TODO These are flips. *)

(** ** Homomorphism Preserving Nullary Operation *)

Class IsNullPres (A B : Type) (X : B -> B -> Prop)
  (x : A) (y : B) (f : A -> B) : Prop :=
  null_pres : X (f x) y.
  (* >: IsFixed *)

(** ** Homomorphism Preserving Unary Operation *)

Class IsUnPres (A B : Type) (X : B -> B -> Prop)
  (f : A -> A) (g : B -> B) (h : A -> B) : Prop :=
  un_pres (x : A) : X (h (f x)) (g (h x)).
  (* =: IsComm *)

(** ** Homomorphism Preserving Binary Operation *)

Class IsBinPres (A B : Type) (X : B -> B -> Prop)
  (k : A -> A -> A) (m : B -> B -> B) (f : A -> B) : Prop :=
  bin_pres (x y : A) : X (f (k x y)) (m (f x) (f y)).
  (* <: IsDistrFns *)
