(** * Contractibility *)

From Coq Require Import
  Classes.Morphisms.
From DEZ Require Export
  Init.

#[local] Open Scope sig_scope.

(** ** Contractible Type *)
(** ** Singleton *)

Class IsContr (A : Type) : Prop :=
  contr : exists x : A, forall y : A, x = y.

Class IsContr' (A : Type) (X : A -> A -> Prop) : Prop :=
  contr' : exists x : A, forall y : A, X x y.

Arguments IsContr' _ _ : clear implicits.

(** ** Fibers of a Unary Function *)

Definition fib (A B : Type) (Y : B -> B -> Prop)
  (f : A -> B) (y : B) : Type :=
  {x : A | Y y (f x)}.

(** ** Contractible Unary Function *)

Equations IsContrFn (A B : Type) (f : A -> B) : Prop :=
  IsContrFn f := forall y : B, IsContr (fib _=_ f y).

Existing Class IsContrFn.

Equations proj1_relation (A : Type) (P : A -> Prop) (X : A -> A -> Prop) :
  relation {x : A | P x} :=
  proj1_relation X (x; a) (y; b) := X x y.

Equations IsContrFn' (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop :=
  IsContrFn' X Y f := forall y : B, IsContr' (fib Y f y) (proj1_relation X).

Existing Class IsContrFn'.
