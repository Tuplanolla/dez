(** * Decidability and Decidable Equality *)

From DEZ Require Export
  Init.

Fail Fail Class HasDec (A : Prop) : Type := {
  decide : bool;
  Decidable_spec : decide = true <-> A;
}.

Notation HasDec := Decidable.

Arguments decide _ {_}.

Typeclasses Transparent decide.

(** The [decide] tactic should have a form
    that accepts a disjunctive pattern with two branches. *)

Tactic Notation "decide" constr(A) "as" "[" ident(a) "|" ident(f) "]" :=
  let x := fresh in
  _decide_ A x; [rename x into a | rename x into f].

Notation HasEqDec := EqDec.

Arguments eq_dec {_ _} _ _.

Typeclasses Transparent EqDec.

Section Context.

Context (A : Type) (Hd : HasEqDec A) (x y : A).

(** We need this instance to bridge the gap
    between the standard library and the equations plugin.
    Without it, we could not [decide (tt = tt)], for example. *)

#[local] Instance has_dec : HasDec (x = y).
Proof.
  destruct (eq_dec x y) as [e | f].
  - exists true. split.
    + intros _. apply e.
    + intros _. reflexivity.
  - exists false. split.
    + intros e. inversion e.
    + intros e. contradiction. Defined.

End Context.

#[export] Hint Resolve has_dec : typeclass_instances.
