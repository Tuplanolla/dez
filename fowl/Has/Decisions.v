(** * Decidability *)

From Coq Require
  Classes.DecidableClass Classes.EquivDec.
From DEZ.Has Require Export
  EquivalenceRelations.
From DEZ.Is Require Export
  Equivalence.
From DEZ.Supports Require Import
  EquivalenceNotations.

(** ** Decidable Proposition *)

Class HasDec (A : Prop) : Type := dec : {A} + {~ A}.

Arguments dec _ {_}.

#[export] Typeclasses Transparent HasDec.

(** We supplement the [decide] tactic with a form
    that accepts a disjunctive pattern with two branches. *)

Tactic Notation "decide" constr(A) "as" "[" ident(x) "|" ident(f) "]" :=
  let a := fresh in _decide_ A a; [rename a into x | rename a into f].

(** We need some instances to bridge the gap
    between our definitions, the standard library and the equations plugin.
    Without them, we could not [decide (tt = tt)], for example. *)

Section Context.

Import Classes.DecidableClass.

Context (A : Prop).

(** Our decidability implies standard library decidability. *)

#[local] Instance has_dec_decidable {d : HasDec A} : Decidable A.
Proof.
  destruct d as [x | f].
  - exists true. intuition.
  - exists false. intuition. Defined.

(** Standard library decidability implies our decidability. *)

#[local] Instance decidable_has_dec {d : Decidable A} : HasDec A.
Proof.
  destruct d as [[] a].
  - left. intuition.
  - right. intuition. Defined.

End Context.

(** ** Decidable Equivalence *)

Class HasEquivDec (A : Type) {X : HasEquivRel A} : Type :=
  equiv_dec (x y : A) : {x == y} + {~ x == y}.

Arguments HasEquivDec _ _ : clear implicits.

#[export] Typeclasses Transparent HasEquivDec.

Section Context.

Import Classes.EquivDec. (** TODO No, use [EqDec] instead? *)

Context (A : Type) (X : A -> A -> Prop).

(** Our decidable equivalence implies
    standard library decidable equivalence. *)

#[local] Instance has_equiv_dec_decidable_equivalence
  {d : HasEquivDec A X} `{IsEq X} : DecidableEquivalence _.
Proof. intros x y. Admitted.

(** Standard library decidable equivalence implies
    our decidable equivalence. *)

#[local] Instance decidable_equivalence_has_equiv_dec
  `{IsEq X} {d : DecidableEquivalence _} : HasEquivDec A X.
Proof. Admitted.

End Context.

(** ** Decidable Equality *)

Fail Fail Class HasEqDec (A : Type) : Type :=
  eq_dec (x y : A) : {x = y} + {x <> y}.

Arguments eq_dec {_ _} _ _.

Notation HasEqDec := EqDec.
Notation eq_dec := eq_dec.

#[export] Typeclasses Transparent HasEqDec.

Section Context.

Context (A : Type).

#[local] Instance equiv_dec_has_eq_dec
  {d : HasEquivDec A _=_} : HasEqDec A := equiv_dec.

#[local] Instance eq_dec_has_equiv_dec
  {d : HasEqDec A} : HasEquivDec A _=_ := eq_dec.

End Context.

Section Context.

Context (A : Type).

#[local] Instance dec_has_eq_dec
  {d : forall x y : A, HasDec (x = y)} : HasEqDec A :=
  fun x y : A => dec (x = y).

#[local] Instance eq_dec_has_dec
  {e : HasEqDec A} (x y : A) : HasDec (x = y) := eq_dec x y.

End Context.
