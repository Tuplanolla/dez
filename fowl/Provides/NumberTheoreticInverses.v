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

Notation "a '<' b" := (a <= b /\ a <> b) (at level 70).

Context (ord_mon : forall (x y z w : B) (l : x <= y) (l' : z <= w), x + z <= y + w).

(** We do not have type classes for successors and predecessors alone,
    which is why we postulate them here.
    We might really just want ring structure on [B]. *)

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
Fail Fail Context (f_surj : forall y : B, exists x : A, y = f x).

(** We care about three of its pseudoinverses,
    that are specified as follows. *)

Context (unf_error : forall (x : B), option A).
Context (unf_error_spec :
  (forall (x : A), unf_error (f x) = Some x) /\
  (forall (x y : B) (e : option_map f (unf_error x) = Some y), x = y)).

Context (unf_down : forall (x : B), A).
Context (unf_down_spec :
  (forall (x : A), unf_down (f x) = x) /\
  (forall (x : B), f (unf_down x) <= x /\ x < f (asuc (unf_down x)))).

Context (unf_remdown : forall (x : B), A + A * B).
Let f_remdown (x : A + A * B) : B :=
  match x with
  | inl a => f a
  | inr (a, b) => b + f a
  end.
Context (unf_remdown_spec :
  (forall (x : B), match unf_remdown x with
    | inl y => True
    | inr (y, z) => f y < z + f y /\ z + f y < f (asuc y)
    end) /\
  (forall (x : A), unf_remdown (f x) = inl x) /\
  (forall (x : B), f_remdown (unf_remdown x) = x)).

(** We implement things in terms of each other.
    Only these really require subtraction,
    decidable equality and some remnant of well-foundedness.
    Everything else can be forced into more general form. *)

(** Possibly-saturative subtraction,
    since monoids have too little and groups have too much. *)

Context (bsub : forall (x y : B), B).

Notation "a '-' b" := (bsub a b).

Definition unf_down_unf_remdown (x : B) : A :=
  match unf_remdown x with
  | inl y => y
  | inr (y, z) => y
  end.

Definition unf_error_unf_remdown (x : B) : option A :=
  match unf_remdown x with
  | inl y => Some y
  | inr (y, z) => None
  end.

Definition unf_remdown_unf_down (x : B) : A + A * B :=
  let y := unf_down x in
  let z := x - f y in
  if eq_dec z 0 then inl y else inr (y, z).

Definition unf_error_unf_down (x : B) : option A :=
  let y := unf_down x in
  if eq_dec (f y) x then Some y else None.

Program Fixpoint unf_remdown_unf_error' (y : option B) (x : B)
  {measure x _<=_} : A + A * B :=
  match unf_error x with
  | Some a =>
    match y with
    | Some b => inr (a, b)
    | None => inl a
    end
  | None => unf_remdown_unf_error' (option_map bsuc y) (bpre x)
  end.
Next Obligation.
  intros a n g x e.
  destruct x as [c |].
  - inversion e.
  - apply bpre_ord. Qed.
Next Obligation. Tactics.program_solve_wf. Defined.

Definition unf_remdown_unf_error (b : B) : A + A * B :=
  unf_remdown_unf_error' None b.

Lemma termination (b : B) : exists a : A, f a < b /\ unf_error b = Some a.
Proof. Admitted.

Program Fixpoint unf_down_unf_error (b : B) {measure b _<=_} : A :=
  match unf_error b with
  | Some a => a
  | None => unf_down_unf_error (bpre b)
  end.
Next Obligation.
  intros b g x e.
  destruct x as [c |].
  - inversion e.
  - apply bpre_ord. Qed.
Next Obligation. Tactics.program_solve_wf. Defined.

(** Secretly, we know these to be true. *)

Lemma eq_unf_down_unf_remdown (x : B) :
  unf_down_unf_remdown x = unf_down x.
Proof. Admitted.

Lemma eq_unf_error_unf_remdown (x : B) :
  unf_error_unf_remdown x = unf_error x.
Proof. Admitted.

Lemma eq_unf_remdown_unf_down (x : B) :
  unf_remdown_unf_down x = unf_remdown x.
Proof. Admitted.

Lemma eq_unf_error_unf_down (x : B) :
  unf_error_unf_down x = unf_error x.
Proof. Admitted.

Lemma eq_unf_remdown_unf_error (x : B) :
  unf_remdown_unf_error x = unf_remdown x.
Proof. Admitted.

Lemma eq_unf_down_unf_error (x : B) :
  unf_down_unf_error x = unf_down x.
Proof. Admitted.

End Context.
 