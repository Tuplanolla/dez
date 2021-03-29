From Maniunfold Require Export
  Init.

(** Unsquashing, large elimination for strict propositions. *)

Class HasUnsquash (A : Type) : Type :=
  unsquash : Squash A -> A.

Hint Mode HasUnsquash ! : typeclass_instances.

Typeclasses Transparent HasUnsquash.

Section Context.

Global Instance not_has_unsquash (A : Prop) : HasUnsquash (~ A).
Proof.
  intros s a. enough sEmpty by contradiction.
  inversion s as [not_a]. contradiction. Qed.

(* Global Instance arrow_has_unsquash (A B : Type)
  `(HasUnsquash B) : HasUnsquash (A -> B).
Proof. intros s a. apply unsquash. inversion s as [f]. apply squash. auto. Qed.
*)

Global Instance pi_has_unsquash (A : Type) (P : A -> Type)
  `(forall a : A, HasUnsquash (P a)) : HasUnsquash (forall a : A, P a).
Proof. intros s a. apply unsquash. inversion s as [f]. apply squash. auto. Qed.

End Context.
