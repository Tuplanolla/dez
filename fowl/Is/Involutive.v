(** * Involutivity *)

From DEZ.Is Require Export
  Reflexive.

(** ** Involutive Element of a Unary Operation *)

Class IsInvolElem (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) : Prop :=
  invol_elem : X (f (f x)) x.

(** ** Involutive Unary Operation *)

Class IsInvol (A : Type) (X : A -> A -> Prop)
  (f : A -> A) : Prop :=
  invol (x : A) : X (f (f x)) x.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (f : A -> A).

(** An element of an involutive unary operation
    is an involutive element of a unary operation. *)

#[export] Instance invol_is_invol_elem
  `{!IsInvol X f} (x : A) : IsInvolElem X x f.
Proof. apply invol. Qed.

End Context.
