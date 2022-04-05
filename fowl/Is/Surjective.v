(** * Surjectivity *)

From DEZ Require Export
  Init.

(** ** Epimorphism *)
(** ** Surjective Unary Function *)

Class IsSurjUnFn (A B : Type) (X : B -> B -> Prop)
  (f : A -> B) : Prop :=
  surj_un_fn (y : B) : exists x : A, X (f x) y.
