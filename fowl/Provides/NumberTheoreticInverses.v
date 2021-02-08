From Coq Require Import
  Lia Lists.List Program.Wf.
From Maniunfold.Has Require Export
  OneSorted.EqualityDecision.
From Maniunfold.Is Require Export
  OneSorted.TotalOrder OneSorted.Monoid.
From Maniunfold.Provides Require Export
  OptionTheorems ProductTheorems.
From Maniunfold.ShouldHave Require Import
  OneSorted.OrderRelationNotations.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Import ListNotations.

(** An adventure in reverse mathematics
    to figure out what structure [A] and [B] need to carry
    for the proofs to go through. *)

Section Context.

Context (A B : Type) (f : A -> B).

Context `{IsTotOrd A} `{IsTotOrd B} `{IsMon B} `{HasEqDec B}.

(** We do not have type classes for successors and predecessors alone,
    which is why we postulate them here. *)

Context (asuc : forall (x : A), A).
Context (bsuc : forall (x : B), B).
Context (bpre : forall (x : B), B).

Notation "'1+' a" := (asuc a) (at level 35).
Notation "'1+' b" := (bsuc b) (at level 35).

(** These properties probably imply more structure anyway. *)

Context (bpre_ord : forall (x : B), bpre x <= x).
Context (b_wf : well_founded _<=_).

(** Our function of interest probably has to be a monotonic injection,
    but this is mere conjecture. *)

Context (f_inj : forall (x y : A) (e : f x = f y), x = y).
Context (f_mono : forall (x y : A) (l : x <= y), f x <= f y).

(** We care about three of its pseudoinverses,
    that are specified as follows. *)

Context (unf_remdown : forall (x : B), A * B).
Context (unf_remdown_spec :
  (forall (x : A), unf_remdown (f x) = (x, 0)) /\
  (forall (x : B), prod_uncurry (_+_ o f) (unf_remdown x) = x) /\
  (forall (x : B), let (y, z) := unf_remdown x in
  bsuc (f y + z) <= f (asuc y))).

Context (unf_down : forall (x : B), A).
Context (unf_down_spec :
  (forall (x : A), unf_down (f x) = x) /\
  (forall (x : B), f (unf_down x) <= x /\ bsuc x <= f (unf_down (bsuc x)))).

Context (unf_error : forall (x : B), option A).
Context (unf_error_spec :
  (forall (x : A), unf_error (f x) = Some x) /\
  (forall (x y : B) (e : option_map f (unf_error x) = Some y), x = y)).

(** Implement things in terms of each other.
    Only these really require subtraction,
    decidable equality and some remnant of well-foundedness.
    Everything else can be forced into more general form. *)

(** Possibly-saturative subtraction,
    since monoids have too little and groups have too much. *)

Context (bsub : forall (x y : B), B).

Definition unf_down_unf_remdown (x : B) : A :=
  let (y, z) := unf_remdown x in y.

Definition unf_error_unf_remdown (x : B) : option A :=
  let (y, z) := unf_remdown x in
  if eq_dec z 0 then Some y else None.

Definition unf_remdown_unf_down (x : B) : A * B :=
  let y := unf_down x in
  (y, bsub x (f y)).

Definition unf_error_unf_down (x : B) : option A :=
  let y := unf_down x in
  if eq_dec (f y) x then Some y else None.

Program Fixpoint unf_remdown_unf_error (a n : B) {measure n _<=_} : A * B :=
  match unf_error n with
  | Some p => (p, a)
  | None => unf_remdown_unf_error (bsuc a) (bpre n)
  end.
Next Obligation.
  intros a n g x e.
  destruct x as [c |].
  - inversion e.
  - apply bpre_ord. Qed.
Next Obligation. Tactics.program_solve_wf. Defined.

Program Fixpoint unf_down_unf_error (n : B) {measure n _<=_} : A :=
  match unf_error n with
  | Some p => p
  | None => unf_down_unf_error (bpre n)
  end.
Next Obligation.
  intros n g x e.
  destruct x as [c |].
  - inversion e.
  - apply bpre_ord. Qed.
Next Obligation. Tactics.program_solve_wf. Defined.

(** Now, let us have a poor attempt at more general interrelations. *)

Lemma eq_unf_down_unf_remdown (x : B) :
  let (y, z) := unf_remdown x in
  unf_down x = y.
Proof.
  destruct unf_remdown_spec as [e0 [e1 e2]].
  destruct unf_down_spec as [e3 e4].
  (* specialize (e0 (unf_down x)). *)
  specialize (e1 x).
  specialize (e2 x).
  destruct (unf_remdown x) as [y z].
  specialize (e0 y).
  specialize (e3 y).
  specialize (e4 (f y)).
  destruct e4 as [e5 e6].
  cbv [prod_uncurry compose fst snd] in e1.
  clear e5.
  rewrite <- e3. f_equal. rewrite <- e1. rewrite <- r_unl. f_equal.
  (* z = 0 *) Admitted.

Lemma eq_unf_error_unf_remdown (x : B) :
  let (y, z) := unf_remdown x in
  (z = 0 -> unf_error x = Some y) /\
  (z <> 0 -> unf_error x = None).
Proof. Admitted.

Lemma eq_unf_remdown_unf_down (x : B) :
  let y := unf_down x in
  forall z : B, f y + z = x ->
  unf_remdown x = (y, z).
Proof. Admitted.

Lemma eq_unf_error_unf_down (x : B) :
  let y := unf_down x in
  (f y = x -> unf_error x = Some y) /\
  (f y <> x -> unf_error x = None).
Proof. Admitted.

Lemma eq_unf_remdown_unf_error (x : B) : True.
Proof. Admitted.

Lemma eq_unf_down_unf_error (x : B) : True.
Proof. Admitted.

End Context.
