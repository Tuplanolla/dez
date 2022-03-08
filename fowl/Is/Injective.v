(** * Injectivity *)

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
