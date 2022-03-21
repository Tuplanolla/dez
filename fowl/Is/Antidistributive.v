(** * Antidistributivity *)

From DEZ.Is Require Export
  Distributive.

(** ** Unary Functions Antidistributing over Binary Functions *)

Class IsAntidistrUnFns (A0 A1 B0 B1 B2 C : Type) (X : C -> C -> Prop)
  (f : A1 -> B0) (g : A0 -> B1) (k : A0 -> A1 -> B2)
  (h : B2 -> C) (m : B0 -> B1 -> C) : Prop :=
  antidistr_un_fns (x : A0) (y : A1) : X (h (k x y)) (m (f y) (g x)).

Section Context.

Context (A0 A1 B0 B1 B2 C : Type) (X : C -> C -> Prop)
  (f : A1 -> B0) (g : A0 -> B1) (k : A0 -> A1 -> B2)
  (h : B2 -> C) (m : B0 -> B1 -> C).

(** Antidistributivity of unary functions over binary functions
    is a special case of the distributivity of their flipped versions. *)

#[export] Instance antidistr_un_fns_is_distr_un_fns_flip
  `{!IsAntidistrUnFns X f g k h m} : IsDistrUnFns X g f k h (flip m).
Proof. auto. Qed.

#[local] Instance distr_un_fns_flip_is_antidistr_un_fns
  `{!IsDistrUnFns X g f k h (flip m)} : IsAntidistrUnFns X f g k h m.
Proof. auto. Qed.

End Context.

(** ** Unary Function Antidistributing over Binary Operations *)

Class IsAntidistrUnFn (A B : Type) (X : B -> B -> Prop)
  (f : A -> B) (k : A -> A -> A) (m : B -> B -> B) : Prop :=
  antidistr_un_fn (x y : A) : X (f (k x y)) (m (f y) (f x)).

Section Context.

Context (A B : Type) (X : B -> B -> Prop)
  (f : A -> B) (k : A -> A -> A) (m : B -> B -> B).

(** Antidistributivity of a unary function over a binary operation
    is a special case of their antidistributivity as functions. *)

#[export] Instance antidistr_un_fn_is_antidistr_un_fns
  `{!IsAntidistrUnFn X f k m} : IsAntidistrUnFns X f f k f m.
Proof. auto. Qed.

#[local] Instance antidistr_un_fns_is_antidistr_un_fn
  `{!IsAntidistrUnFns X f f k f m} : IsAntidistrUnFn X f k m.
Proof. auto. Qed.

End Context.

(** ** Unary Operation Antidistributing over a Binary Operation *)

(** This has the same shape as [Z.opp_add_antidistr]. *)

Class IsAntidistrUnOp (A : Type) (X : A -> A -> Prop)
  (f : A -> A) (k : A -> A -> A) : Prop :=
  antidistr_un_op (x y : A) : X (f (k x y)) (k (f y) (f x)).

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (f : A -> A) (k : A -> A -> A).

(** Antidistributivity of a unary operation over a binary operation
    is a special case of their antidistributivity as functions. *)

#[export] Instance antidistr_un_op_is_antidistr_un_fns
  `{!IsAntidistrUnOp X f k} : IsAntidistrUnFns X f f k f k.
Proof. auto. Qed.

#[local] Instance antidistr_un_fns_is_antidistr_un_op
  `{!IsAntidistrUnFns X f f k f k} : IsAntidistrUnOp X f k.
Proof. auto. Qed.

End Context.
