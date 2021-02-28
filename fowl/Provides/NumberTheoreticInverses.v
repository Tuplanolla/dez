From Coq Require Import
  Lia Lists.List NArith.NArith ZArith.ZArith Program.Wf.
From Maniunfold.Has Require Export
  OneSorted.EqualityDecision.
From Maniunfold.Is Require Export
  OneSorted.TotalOrder OneSorted.Monoid.
From Maniunfold.Provides Require Export
  OptionTheorems ProductTheorems.
(* From Maniunfold.ShouldHave Require Import
  OneSorted.OrderRelationNotations. *)
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Import ListNotations.

(** An adventure in reverse mathematics
    to figure out what structure [A] and [B] need to carry
    for the proofs to go through. *)

Section Context.

Local Open Scope N_scope.
Local Open Scope Z_scope.

Let A : Type := N.
Let B : Type := Z.

(** Our function of interest probably has to be a monotonic injection,
    but this is mere conjecture. *)

Context (f : A -> B).
Arguments f _%N.
Context (f_inj : forall (a b : A) (e : f a = f b), a = b).
Context (f_mono : forall (a b : A) (l : (a <= b)%N), f a <= f b).
Fail Fail Context (f_surj : forall b : B, exists a : A, b = f a).

(** We care about three of its pseudoinverses,
    that are specified as follows. *)

Context (unf_error : B -> option A).
Arguments unf_error _%Z.
Class unf_error_spec : Prop := {
  here_error : forall a : A, unf_error (f a) = Some a;
  there_error : forall (x y : B) (e : option_map f (unf_error x) = Some y),
    x = y;
}.
(** This is equally strong. *)
Class unf_error_spec' : Prop := {
  here_error' : forall a : A, unf_error (f a) = Some a;
  there_error' : forall (a : A) (b : B) (e : unf_error b = Some a), f a = b;
}.
Lemma from_burritos_strength : unf_error_spec <-> unf_error_spec'.
Proof.
  split; intros ?; constructor.
  - intros a. rewrite here_error. reflexivity.
  - intros a b e. symmetry. apply there_error.
    rewrite e. cbv [option_map]. reflexivity.
  - intros a. rewrite here_error'. reflexivity.
  - intros x y e. destruct (unf_error x) as [a |] eqn : e'.
    apply there_error' in e'. cbv [option_map] in e.
    injection e. clear e. intros e. transitivity (f a); auto.
    inversion e. Qed.
(** As demonstrated. *)
Corollary elsehere_error `{unf_error_spec} :
  forall x : option A, let y := option_map f x in
  option_map f (option_bind unf_error y) = y.
Proof.
  intros [a |].
  - cbv zeta. cbv [option_map option_bind]. rewrite here_error. reflexivity.
  - cbv zeta. cbv [option_map option_bind]. reflexivity. Qed.
Corollary elsethere_error `{unf_error_spec} :
  forall x : option B, let y := option_bind unf_error x in
  option_bind unf_error (option_map f y) = y.
Proof.
  intros [b |].
  - cbv zeta. cbv [option_map option_bind]. destruct (unf_error b) as [a |].
    + rewrite here_error. reflexivity.
    + reflexivity.
  - cbv zeta. cbv [option_map option_bind]. reflexivity. Qed.
(** We did not need [there_error], which is suspicious.
    Try a stronger version! *)
Corollary elsethere_error' `{unf_error_spec} :
  forall x : option A, option_bind unf_error (option_map f x) = x.
Proof.
  intros [a |].
  - cbv [option_map option_bind]. rewrite here_error. reflexivity.
  - cbv [option_map option_bind]. reflexivity. Qed.
(** Curses!
    Foiled again! *)

Context (unf_down : B -> A).
Arguments unf_down _%Z.
Class unf_down_spec : Prop := {
  here_down : forall a : A, unf_down (f a) = a;
  there_down : forall b : B, f (unf_down b) <= b < f (1 + unf_down b);
}.

Definition B_quot : Type := {b : B ! Squash (f (unf_down b) = b)}.
Program Definition B_pr `{unf_down_spec} (b : B) : B_quot :=
  Sexists _ (f (unf_down b)) _.
Next Obligation. intros ? b. apply squash. rewrite here_down. reflexivity. Qed.
Context (unf_downdep : B_quot -> A).
Class unf_downdep_spec `{unf_down_spec} : Prop := {
  here_downdep : forall a : A, unf_downdep (B_pr (f a)) = a;
  there_downdep : forall x : B_quot, B_pr (f (unf_downdep x)) = x;
}.

Definition f_remdown (x : A + A * B) : B :=
  match x with
  | inl a => f a
  | inr (a, b) => b + f a
  end.
Context (unf_remdown : B -> A + A * B).
Class unf_remdown_spec : Prop := {
  refine_remdown : forall x : B,
    match unf_remdown x with
    | inl a => True
    | inr (a, b) => f a < b + f a < f (1 + a)
    end;
  here_remdown : forall a : A, unf_remdown (f a) = inl a;
  there_remdown : forall b : B, f_remdown (unf_remdown b) = b;
}.
Remark not_elsehere_remdowndep `{unf_remdown_spec} :
  ~ forall x : A + A * B, unf_remdown (f_remdown x) = x.
Proof.
  intros e.
  assert (a : A) by constructor.
  specialize (e (inr (a, 0%Z))).
  pose proof refine_remdown (f_remdown (inr (a, 0%Z))) as l.
  rewrite e in l.
  lia. Qed.

Definition C : Type := A + {x : A * B ! let (a, b) := x in
  Squash (f a < b + f a < f (1 + a))}.
Definition f_remdowndep (x : C) : B :=
  match x with
  | inl a => f a
  | inr (Sexists _ (a, b) _) => b + f a
  end.
Context (unf_remdowndep : B -> C).
Class unf_remdowndep_spec : Prop := {
  here_remdowndep : forall a : A, unf_remdowndep (f a) = inl a;
  there_remdowndep : forall b : B, f_remdowndep (unf_remdowndep b) = b;
}.
Corollary elsehere_remdowndep `{unf_remdowndep_spec} :
  forall x : C, unf_remdowndep (f_remdowndep x) = x.
Proof.
  intros [a | [[a b] e]].
  - cbv [f_remdowndep]. rewrite here_remdowndep. reflexivity.
  - cbv [f_remdowndep].
    destruct (unf_remdowndep (b + f a)) as [a' | [[a' b'] e']] eqn : e''.
    exfalso. admit. f_equal. apply Spr1_inj. cbv [Spr1]. admit. Abort.

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
 