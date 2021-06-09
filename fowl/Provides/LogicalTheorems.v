(** * Basic Logic *)

From Coq Require Import
  Classes.DecidableClass.
From Maniunfold.Has Require Export
  Unsquashing.

Lemma f_nequal (A B : Type) (f : A -> B) (x y : A) (fxy : f x <> f y) : x <> y.
Proof. auto using f_equal. Qed.

Section Context.

Context (A : Prop) `(Decidable A).

Global Instance decidable_has_unsquash : HasUnsquash A.
Proof.
  intros s. decide A as a; [| rename a into f].
  - assumption.
  - enough sEmpty by contradiction. inversion s as [a]. contradiction. Qed.

End Context.
