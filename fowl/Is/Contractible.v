(** * Contractibility *)

From DEZ Require Export
  Init.

(** ** Contractible Type *)
(** ** Singleton *)

Class IsContr (A : Type) : Prop :=
  contr : exists x : A, forall y : A, x = y.

(** ** Fibers of a Unary Function *)

Definition fib (A B : Type) (X : B -> B -> Prop)
  (f : A -> B) (y : B) : Type :=
  {x : A | X (f x) y}.

(** ** Contractible Unary Function *)

Equations IsContrFn (A B : Type) (X : B -> B -> Prop) (f : A -> B) : Prop :=
  IsContrFn X f := forall y : B, IsContr (fib X f y).

Existing Class IsContrFn.
