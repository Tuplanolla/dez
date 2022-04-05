(** * Surjectivity *)

From DEZ Require Export
  Init.

(** ** Epimorphism *)
(** ** Surjective Unary Function *)

Class IsSurjUnFn (A B : Type) (X : B -> B -> Prop)
  (f : A -> B) : Prop :=
  surj_un_fn (y : B) : exists x : A, X (f x) y.

(** ** Surjective Unary Operation *)

Class IsSurj (A : Type) (X : A -> A -> Prop)
  (f : A -> A) : Prop :=
  surj (y : A) : exists x : A, X (f x) y.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (f : A -> A).

(** Surjectivity of a unary operation is a special case
    of its surjectivity as a unary function. *)

#[export] Instance surj_is_surj_un_fn
  `{!IsSurj X f} : IsSurjUnFn X f.
Proof. auto. Qed.

#[local] Instance surj_un_fn_is_surj
  `{!IsSurjUnFn X f} : IsSurj X f.
Proof. auto. Qed.

End Context.
