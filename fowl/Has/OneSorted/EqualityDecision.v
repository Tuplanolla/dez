From Coq Require Import
  Logic.Eqdep_dec.
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
