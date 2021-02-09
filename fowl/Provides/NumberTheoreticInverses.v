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

(** We care about three of its pseudoinverses,
    that are specified as follows. *)

Context (unf_remdown : forall (x : B), A * B).
Context (unf_remdown_spec :
  (forall (x : A), unf_remdown (f x) = (x, 0)) /\
  (forall (x : B), prod_uncurry (flip _+_ o f) (unf_remdown x) = x) /\
  (forall (x : B), let (y, z) := unf_remdown x in
    0 <= z /\ z + f y < f (asuc y))).
    (* 0 <= z /\ bsuc (z + f y) <= f (asuc y))). *)

Context (unf_down : forall (x : B), A).
Context (unf_down_spec :
  (forall (x : A), unf_down (f x) = x) /\
  (forall (x : B), f (unf_down x) <= x /\
    x < f (asuc (unf_down x)))).
  (* (forall (x : B), f (unf_down x) <= x /\ bsuc x <= f (asuc (unf_down x)))). *)

Context (unf_error : forall (x : B), option A).
Context (unf_error_spec :
  (forall (x : A), unf_error (f x) = Some x) /\
  (forall (x y : B) (e : option_map f (unf_error x) = Some y), x = y)).

(** Knowing these should suffice to relate the definitions. *)

Context (rel_down_remdown :
  forall (x : B), let (y, z) := unf_remdown x in
  unf_down x = y).
Context (rel_error_remdown :
  forall (x : B), let (y, z) := unf_remdown x in
  (z = 0 -> unf_error x = Some y) /\
  (z <> 0 -> unf_error x = None)).

(** We should be able to prove [unf_down_spec]
    from [unf_remdown_spec] and [rel_down_remdown] and [rel_error_remdown].
    ...and all the five other directions too. *)

Lemma case_0 : (forall (x : A), unf_down (f x) = x) /\
  (forall (x : B), f (unf_down x) <= x /\ x < f (asuc (unf_down x))).
Proof. clear unf_down_spec unf_error_spec.
  split.
  - intros x.
    destruct unf_remdown_spec as [e0 [e1 e2]].
    pose proof rel_down_remdown as e3.
    specialize (e0 x).
    specialize (e1 (f x)).
    specialize (e2 (f x)).
    specialize (e3 (f x)).
    destruct (unf_remdown (f x)) as [y z] eqn : e.
    rewrite e3. inversion e0. auto.
  - intros x. repeat split.
    + destruct unf_remdown_spec as [e0 [e1 e2]].
      pose proof rel_down_remdown as e3.
      specialize (e0 (unf_down x)).
      specialize (e1 x).
      specialize (e2 x).
      specialize (e3 x).
      cbv [prod_uncurry compose flip fst snd] in e1.
      destruct (unf_remdown x) as [y z] eqn : e.
      destruct e2 as [e4 e5].
      rewrite e3. rewrite <- e1. rewrite <- (l_unl (f y)) at 1.
      apply ord_mon. apply e4. apply refl.
    + destruct unf_remdown_spec as [e0 [e1 e2]].
      pose proof rel_down_remdown as e3.
      specialize (e1 x).
      specialize (e2 x).
      specialize (e3 x).
      cbv [prod_uncurry compose flip fst snd] in e1.
      destruct (unf_remdown x) as [y z] eqn : e.
      specialize (e0 y).
      destruct e2 as [e4 [e5 e6]].
      rewrite e1 in e5, e6. rewrite e3. apply e5.
    + destruct unf_remdown_spec as [e0 [e1 e2]].
      pose proof rel_down_remdown as e3.
      specialize (e1 x).
      specialize (e2 x).
      specialize (e3 x).
      cbv [prod_uncurry compose flip fst snd] in e1.
      destruct (unf_remdown x) as [y z] eqn : e.
      specialize (e0 y).
      destruct e2 as [e4 [e5 e6]].
      rewrite e1 in e5, e6. rewrite e3. apply e6. Qed.

Lemma case_1 : (forall (x : A), unf_error (f x) = Some x) /\
  (forall (x y : B) (e : option_map f (unf_error x) = Some y), x = y).
Proof. clear unf_down_spec unf_error_spec.
  split.
  - intros x.
    destruct unf_remdown_spec as [e0 [e1 e2]].
    pose proof rel_error_remdown as e3.
    specialize (e0 x).
    specialize (e1 (f x)).
    specialize (e2 (f x)).
    specialize (e3 (f x)).
    destruct (unf_remdown (f x)) as [y z] eqn : e.
    inversion e0; subst.
    cbv [prod_uncurry compose flip fst snd] in e1.
    destruct e2 as [e4 e6]. destruct e3 as [e7 e8].
    apply e7. auto.
  - intros x a ea.
    destruct unf_remdown_spec as [e0 [e1 e2]].
    pose proof rel_error_remdown as e3.
    specialize (e1 x).
    specialize (e2 x).
    specialize (e3 x).
    cbv [prod_uncurry compose flip fst snd] in e1.
    destruct (unf_remdown x) as [y z] eqn : e.
    specialize (e0 y).
    destruct e2 as [e4 e6].
    destruct e3 as [e7 e8].
    destruct (eq_dec z 0).
    + subst. rewrite l_unl in *.
      rewrite (e7 (eq_refl 0)) in ea.
      cbv [option_map] in ea.
      inversion ea. auto.
    + rewrite (e8 n) in ea.
      cbv [option_map] in ea.
      inversion ea. Qed.

Lemma case_2 : (forall (x : A), unf_remdown (f x) = (x, 0)) /\
  (forall (x : B), prod_uncurry (flip _+_ o f) (unf_remdown x) = x) /\
  (forall (x : B), let (y, z) := unf_remdown x in
    0 < z /\ z + f y < f (asuc y)).
Proof. clear unf_remdown_spec unf_error_spec.
  repeat split.
  - intros x.
    destruct unf_down_spec as [e0 e1].
    pose proof rel_down_remdown as e3.
    specialize (e0 x).
    specialize (e1 (f x)).
    destruct e1 as [e4 e5].
    specialize (e3 (f x)).
    destruct (unf_remdown (f x)) as [y z] eqn : e.
    rewrite <- e0, <- e3. f_equal. admit. (* impossible without knowing more *)
  - intros x.
    cbv [prod_uncurry compose flip fst snd].
    destruct unf_down_spec as [e0 e1].
    pose proof rel_down_remdown as e3.
    specialize (e1 x).
    specialize (e3 x).
    destruct (unf_remdown x) as [y z] eqn : e.
    specialize (e0 y).
    destruct e1 as [e7 e8]. admit. Abort.

(** We implement things in terms of each other.
    Only these really require subtraction,
    decidable equality and some remnant of well-foundedness.
    Everything else can be forced into more general form. *)

(** Possibly-saturative subtraction,
    since monoids have too little and groups have too much. *)

Context (bsub : forall (x y : B), B).

Notation "a '-' b" := (bsub a b).

Definition unf_down_unf_remdown (x : B) : A :=
  let (y, z) := unf_remdown x in y.

Definition unf_error_unf_remdown (x : B) : option A :=
  let (y, z) := unf_remdown x in
  if eq_dec z 0 then Some y else None.

Definition unf_remdown_unf_down (x : B) : A * B :=
  let y := unf_down x in
  (y, x - f y).

Definition unf_error_unf_down (x : B) : option A :=
  let y := unf_down x in
  if eq_dec (f y) x then Some y else None.

Program Fixpoint unf_remdown_unf_error' (a n : B) {measure n _<=_} : A * B :=
  match unf_error n with
  | Some p => (p, a)
  | None => unf_remdown_unf_error' (bsuc a) (bpre n)
  end.
Next Obligation.
  intros a n g x e.
  destruct x as [c |].
  - inversion e.
  - apply bpre_ord. Qed.
Next Obligation. Tactics.program_solve_wf. Defined.

Definition unf_remdown_unf_error (n : B) : A * B := unf_remdown_unf_error' 0 n.

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
