(** * Isomorphism or Equivalence or Bijection *)

From Maniunfold.Is Require Export
  Inverse.

Class IsIso (A B : Type) (f : A -> B) (g : B -> A) : Prop := {
  is_inv_l :> IsInvL f g;
  is_inv_r :> IsInvR f g;
}.

Module Flipped.

Section Context.

Context (A B : Type) (f : A -> B) (g : B -> A) `(!IsIso f g).

#[local] Instance is_iso : IsIso g f.
Proof.
  split.
  - intros b. apply inv_r.
  - intros a. apply inv_l. Qed.

End Context.

#[export] Hint Resolve is_iso : typeclass_instances.

End Flipped.
