From Coq Require Import
  Classes.DecidableClass Logic.Eqdep_dec.
From Maniunfold.Has Require Export
  OneSorted.Decision OneSorted.ProofIrrelevance.

(** Equality decision, decidable equality.
    Commonly found in discrete structures. *)

Class HasEqDec (A : Type) : Type :=
  eq_dec : forall x y : A, {x = y} + {x <> y}.

Hint Mode HasEqDec ! : typeclass_instances.

Typeclasses Transparent HasEqDec.

Section Context.

Context (A : Type) `(HasEqDec A).

Global Instance eq_has_dec (x y : A) : HasDec (x = y) := eq_dec x y.

Global Instance eq_has_prf_irrel (x y : A) : HasPrfIrrel (x = y).
Proof. intros ? ?. apply UIP_dec. assumption. Qed.

End Context.

Section Context.

Context (A : Type) `(HasEqDec A).

Global Program Instance eq_has_decidable (x y : A) : Decidable (x = y) := {
  Decidable_witness := proj1_sig (Sumbool.bool_of_sumbool (eq_dec x y));
  Decidable_spec := _;
}.
Next Obligation.
  intros x y. destruct (eq_dec x y).
  - split; auto.
  - split; cbn; congruence. Qed.

End Context.
