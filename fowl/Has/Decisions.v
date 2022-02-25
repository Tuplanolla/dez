(** * Decidability *)

From Coq Require
  Classes.DecidableClass Classes.EquivDec.
From DEZ Require Export
  Init.
From DEZ.Has Require Export
  EquivalenceRelations.

(** TODO This is in disrepair, but otherwise we are doing good! *)

(* From DEZ.ShouldHave Require Import
  EquivalenceRelationNotations. *)
Declare Scope relation_scope.
Delimit Scope relation_scope with rel.

#[export] Open Scope relation_scope.

Notation "'_==_'" := eq_rel : relation_scope.
Notation "x '==' y" := (eq_rel x y) : relation_scope.

(* Classes.DecidableClass.Decidable *)
(* Classes.EquivDec.DecidableEquivalence *)

(** ** Decidable Proposition *)

Class HasDec (A : Prop) : Type := dec : {A} + {~ A}.

Arguments dec _ {_}.

#[export] Typeclasses Transparent HasDec.

(** The [decide] tactic should have a form
    that accepts a disjunctive pattern with two branches. *)

Tactic Notation "decide" constr(A) "as" "[" ident(a) "|" ident(f) "]" :=
  let x := fresh in
  _decide_ A x; [rename x into a | rename x into f].

(** ** Decidable Equivalence *)

Class HasEquivDec (A : Type) {X : HasEqRel A} : Type :=
  equiv_dec (x y : A) : {x == y} + {~ x == y}.

#[export] Typeclasses Transparent HasEquivDec.

(** ** Decidable Equality *)

Fail Fail Class HasEqDec (A : Type) : Type :=
  eq_dec (x y : A) : {x = y} + {x <> y}.

Notation HasEqDec := EqDec.

#[export] Typeclasses Transparent HasEqDec.

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
