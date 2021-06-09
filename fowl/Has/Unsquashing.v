(** * Unsquashing, Large Elimination for Strict Propositions *)

From Maniunfold Require Export
  Init.

Class HasUnsquash (A : Type) : Type := unsquash (x : Squash A) : A.

Typeclasses Transparent HasUnsquash.

Section Context.

#[local] Instance not_has_unsquash (A : Prop) : HasUnsquash (~ A).
Proof.
  intros x a.
  enough sEmpty by contradiction.
  inversion x as [f].
  contradiction. Qed.

#[local] Instance notT_has_unsquash (A : Type) : HasUnsquash (- A).
Proof.
  intros x a.
  enough sEmpty by contradiction.
  inversion x as [f].
  contradiction. Qed.

#[local] Instance arrow_has_unsquash (A B : Type)
  `(HasUnsquash B) : HasUnsquash (A -> B).
Proof.
  intros x a.
  apply unsquash.
  inversion x as [f].
  apply squash.
  auto. Qed.

#[local] Instance pi_has_unsquash (A : Type) (P : A -> Type)
  `(forall a : A, HasUnsquash (P a)) : HasUnsquash (forall a : A, P a).
Proof.
  intros x a.
  apply unsquash.
  inversion x as [f].
  apply squash.
  auto. Qed.

End Context.

#[export] Hint Resolve not_has_unsquash notT_has_unsquash
  arrow_has_unsquash pi_has_unsquash : typeclass_instances.
