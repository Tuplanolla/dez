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

Class HasContr (A : Type) (X : A -> A -> Prop) : Type :=
  contr : {x : A | forall y : A, X x y}.

Arguments HasContr _ _ : clear implicits.

Class IsContr (A : Type) (X : A -> A -> Prop) : Prop :=
  contr_prop : exists x : A, forall y : A, X x y.

Arguments IsContr _ _ : clear implicits.

Section Context.

Context (A B : Type) (X : A -> A -> Prop).

#[local] Instance contr_is_contr
  `{!HasContr A X} : IsContr A X.
Proof. destruct contr; esplit; eauto. Qed.

End Context.

(** ** Fibers of a Unary Function *)

Definition fib (A B : Type) (Y : B -> B -> Prop)
  (f : A -> B) (y : B) : Type :=
  {x : A | Y y (f x)}.

(** ** Contractible Unary Function *)

Equations HasContrFn (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Type :=
  HasContrFn X Y f := forall y : B, HasContr (fib Y f y) (proj1_sig_relation X).

Existing Class HasContrFn.

Equations IsContrFn (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B) : Prop :=
  IsContrFn X Y f := forall y : B, IsContr (fib Y f y) (proj1_sig_relation X).

Existing Class IsContrFn.

Section Context.

Context (A B : Type) (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B).

#[local] Instance contr_fn_is_contr_fn
  `{!HasContrFn X Y f} : IsContrFn X Y f.
Proof.
  match goal with
  | x : HasContrFn _ _ _ |- _ => rename x into HCF
  end.
  intros y. destruct (HCF y); esplit; eauto.
Qed.

End Context.

Section Context.

Context (A B : Type)
  (X : A -> A -> Prop) (Y : B -> B -> Prop)
  (f : A -> B).

#[local] Instance contr_fn_has_contr_fib
  `{!HasContrFn X Y f} (y : B) : HasContr (fib Y f y) (proj1_sig_relation X).
Proof. eauto. Qed.

#[local] Instance contr_fib_has_contr_fn
  `{!forall y : B, HasContr (fib Y f y) (proj1_sig_relation X)} :
  HasContrFn X Y f.
Proof. eauto. Qed.

End Context.
