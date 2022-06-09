(** * Contractibility *)

From Coq Require Import
  Classes.Morphisms.
From DEZ Require Export
  Init.

#[local] Open Scope sig_scope.

Equations proj1_sig_relation (A : Type) (P : A -> Prop) (X : A -> A -> Prop) :
  relation {x : A | P x} :=
  proj1_sig_relation X (x; a) (y; b) := X x y.

#[local] Open Scope Ssig_scope.

Equations Spr1_relation (A : Type) (P : A -> SProp) (X : A -> A -> Prop) :
  relation {x : A $ P x} :=
  Spr1_relation X (x; a) (y; b) := X x y.

(** ** Contractible Type *)
(** ** Singleton *)

Class IsContr (A : Type) (X : A -> A -> Prop) : Prop :=
  contr : exists x : A, forall y : A, X x y.

Arguments IsContr _ _ : clear implicits.

(** ** Fibers of a Unary Function *)

Definition fib (A B : Type) (Y : B -> B -> Prop)
  (f : A -> B) (y : B) : Type :=
  {x : A | Y y (f x)}.

(** ** Contractible Unary Function *)

Equations IsContrFn (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop :=
  IsContrFn X Y f := forall y : B, IsContr (fib Y f y) (proj1_sig_relation X).

Existing Class IsContrFn.

Section Context.

Context (A B : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B).

#[local] Instance contr_fn_is_contr_fib
  `{!IsContrFn X Y f} (y : B) : IsContr (fib Y f y) (proj1_sig_relation X).
Proof. eauto. Qed.

#[local] Instance contr_fib_is_contr_fn
  `{!forall y : B, IsContr (fib Y f y) (proj1_sig_relation X)} :
  IsContrFn X Y f.
Proof. eauto. Qed.

Lemma contr_fn_iff_contr_fib : 
  IsContrFn X Y f <-> forall y : B, IsContr (fib Y f y) (proj1_sig_relation X).
Proof. esplit; typeclasses eauto. Qed.
