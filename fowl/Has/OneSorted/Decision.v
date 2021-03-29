From Maniunfold.Has Require Export
  Unsquashing.

(** Decision, decidable proposition. *)

#[deprecated]
Class HasDec (A : Prop) : Type := dec : {A} + {~ A}.

Hint Mode HasDec ! : typeclass_instances.

Typeclasses Transparent HasDec.

Arguments dec _ {_}.

Section Context.

Context (A : Prop) `(HasDec A).

Global Instance A_has_unsquash : HasUnsquash A.
Proof.
  intros s. destruct (dec A) as [a | not_a].
  - assumption.
  - enough sEmpty by contradiction. inversion s as [a]. contradiction. Qed.

End Context.
