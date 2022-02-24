(* maybe *)
(** * Decidability and Decidable Equality *)

From DEZ Require Export
  Init.

Class HasDec (A : Prop) : Type := dec : {A} + {~ A}.

#[export] Typeclasses Transparent HasDec.

(** The [decide] tactic should have a form
    that accepts a disjunctive pattern with two branches. *)

Tactic Notation "decide" constr(A) "as" "[" ident(a) "|" ident(f) "]" :=
  let x := fresh in
  _decide_ A x; [rename x into a | rename x into f].

Notation HasEqDec := EqDec.

Arguments eq_dec {_ _} _ _.

#[export] Typeclasses Transparent EqDec.

(** We need some instances to bridge the gap
    between our definition, the standard library and the equations plugin.
    Without them, we could not [decide (tt = tt)], for example. *)

Section Context.

Context (A : Prop).

#[local] Instance has_dec (d : Decidable A) : HasDec A.
Proof.
  destruct d as [[] ?].
  - left. intuition.
  - right. intuition. Defined.

#[local] Instance decidable (d : HasDec A) : Decidable A.
Proof.
  destruct d as [x | f].
  - exists true. intuition.
  - exists false. split.
    + congruence.
    + intuition. Defined.

End Context.

#[export] Hint Resolve decidable : typeclass_instances.

Section Context.

Context (A : Type).

#[local] Instance has_eq_dec (d : forall x y : A, HasDec (x = y)) :
  HasEqDec A := d.

#[local] Instance eq_has_dec (e : HasEqDec A) (x y : A) :
  HasDec (x = y) := e x y.

End Context.

#[export] Hint Resolve eq_has_dec : typeclass_instances.
