(** * Injectivity *)

From DEZ Require Export
  Init.

(** ** Injective Unary Function *)

Class IsInjUnFn (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop :=
  inj_un_fn (x y : A) (a : Y (f x) (f y)) : X x y.

(** ** Cancellative Unary Operation *)
(** ** Injective Unary Operation *)

Class IsInj (A : Type) (X : A -> A -> Prop) (f : A -> A) : Prop :=
  inj (x y : A) (a : X (f x) (f y)) : X x y.

Section Context.

Context (A : Type) (X : A -> A -> Prop) (f : A -> A).

(** Injective binary operations are special cases of injective functions. *)

#[export] Instance inj_un_fn_is_inj
  `{!IsInjUnFn X X f} : IsInj X f.
Proof. auto. Qed.

#[local] Instance inj_is_inj_un_fn
  `{!IsInj X f} : IsInjUnFn X X f.
Proof. auto. Qed.

End Context.
