(** * Decidability *)

From Coq Require
  Classes.DecidableClass Classes.EquivDec Classes.SetoidDec.
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

(** We need some instances to bridge the gap between our definitions,
    standard library definitions and equations plugin definitions.
    We explicitly export instances of existing classes,
    so that we can invoke existing tactics,
    such as [decide (tt = tt)]. *)

Section Context.

Import Classes.DecidableClass.

Context (A : Prop).

(** Our decidability implies standard library decidability. *)

#[local] Instance dec_decidable {d : HasDec A} : Decidable A.
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

Arguments HasEquivDec _ {_}.

#[export] Typeclasses Transparent HasEquivDec.

Section Context.

Import Classes.EquivDec.

Context (A : Type) {X : HasEquivRel A} `{!IsEquiv X}.

(** Our decidable equivalence implies
    standard library decidable equivalence. *)

#[local] Instance equiv_dec_eq_dec
  {e : HasEquivDec A} : EqDec A _==_ := e.

(** Standard library decidable equivalence implies
    our decidable equivalence. *)

#[local] Instance eq_dec_has_equiv_dec
  {e : EqDec A _==_} : HasEquivDec A := e.

End Context.

Section Context.

Import Classes.SetoidDec.

Context (A : Type) {X : HasEquivRel A} `{!IsEquiv X}.

(** Our decidable equivalence implies
    standard library decidable equivalence. *)

#[local] Instance equiv_dec_eq_dec_equiv
  {e : HasEquivDec A} : EqDec {| equiv := _==_ |} := e.

(** Standard library decidable equivalence implies
    our decidable equivalence. *)

#[local] Instance eq_dec_equiv_has_equiv_dec
  {e : EqDec {| equiv := _==_ |}} : HasEquivDec A := e.

End Context.

Section Context.

Context (A : Type) {X : HasEquivRel A}.

(** Decidable equivalence implies decidability of equivalences. *)

#[export] Instance equiv_dec_has_dec_equiv
  {e : HasEquivDec A} (x y : A) : HasDec (x == y) := equiv_dec x y.

(** Decidability of equivalences implies decidable equivalence. *)

#[local] Instance dec_equiv_has_equiv_dec
  {d : forall x y : A, HasDec (x == y)} : HasEquivDec A :=
  fun x y : A => dec (x == y).

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

(** Decidable equality implies decidability of equalities. *)

#[export] Instance eq_dec_has_dec_eq
  {e : HasEqDec A} (x y : A) : HasDec (x = y) := eq_dec x y.

(** Decidability of equalities implies decidable equality. *)

#[local] Instance dec_eq_has_eq_dec
  {d : forall x y : A, HasDec (x = y)} : HasEqDec A :=
  fun x y : A => dec (x = y).

End Context.

Section Context.

Context (A : Type).

(** Decidable equality implies decidable equivalence over equality. *)

#[export] Instance eq_dec_has_equiv_dec_eq
  {e : HasEqDec A} : HasEquivDec A (X := _=_) := eq_dec.

(** Decidable equivalence over equality implies decidable equality. *)

#[local] Instance equiv_dec_eq_has_eq_dec
  {e : HasEquivDec A (X := _=_)} : HasEqDec A := equiv_dec.

End Context.
