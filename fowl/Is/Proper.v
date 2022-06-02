(** * Properness and Respectfulness *)

From Coq Require Import
  Classes.Morphisms.
From DEZ Require Export
  Init.

(** ** Proper Relation *)
(** ** Respectful Morphism *)

Fail Fail Class IsProper (A : Type) (X : A -> A -> Prop) : Prop :=
  proper (x : A) : X x x.

Arguments Proper {_} _ _.
Arguments proper_prf {_ _} _ {_}.

Notation IsProper := Proper.
Notation proper := proper_prf.

Section Context.

Context (A : Type) (X : A -> A -> Prop).

(** A constant function is proper. *)

#[export] Instance proper_const : IsProper (X ==> X ==> X) const.
Proof. intros x y a z w b. unfold const. apply a. Qed.

Arguments proper_const [_ _] _ [_ _] _.

End Context.
