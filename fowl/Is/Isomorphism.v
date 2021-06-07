(** Isomorphism, Equivalence, Bijection *)

From Maniunfold Require Export
  Init.

Class IsIso (A B : Type) (f : A -> B) (g : B -> A) : Prop := {
  sect (a : A) : g (f a) = a;
  retr (b : B) : f (g b) = b;
}.

Section Context.

Context (A B : Type) (f : A -> B) (g : B -> A) `(!IsIso f g).

#[local] Instance is_iso : IsIso g f.
Proof.
  split.
  - intros b. apply retr.
  - intros a. apply sect. Qed.

End Context.
