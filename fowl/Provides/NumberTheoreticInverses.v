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

Local Open Scope Z_scope.
Local Open Scope N_scope.

Let A : Type := Z.
Let B : Type := N.

(** Our function of interest probably has to be a monotonic injection,
    but this is mere conjecture. *)

Context (f : A -> B).
Arguments f _%Z.
Context (f_inj : forall (x y : A) (e : f x = f y), x = y).
Context (f_mono : forall (x y : A) (l : (x <= y)%Z), f x <= f y).
Fail Fail Context (f_surj : forall b : B, exists a : A, b = f a).

(** We care about three of its pseudoinverses,
    that are specified as follows. *)

Context (unf_error : B -> option A).
Arguments unf_error _%N.
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
Arguments unf_down _%N.
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
Arguments unf_remdown _%N.
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
  specialize (e (inr (a, 0))).
  pose proof refine_remdown (f_remdown (inr (a, 0))) as l.
  rewrite e in l.
  lia. Qed.

Definition P (a : A) (b : B) : Prop := f a < b + f a < f (1 + a).
Definition A_sub : Type := A + {x : A * B ! Squash (prod_uncurry P x)}.
Definition f_remdowndep (x : A_sub) : B :=
  match x with
  | inl a => f a
  | inr (Sexists _ (a, b) _) => b + f a
  end.
Context (unf_remdowndep : B -> A_sub).
Class unf_remdowndep_spec : Prop := {
  here_remdowndep : forall x : A_sub, unf_remdowndep (f_remdowndep x) = x;
  there_remdowndep : forall b : B, f_remdowndep (unf_remdowndep b) = b;
}.

End Context.

Section Context.

Local Open Scope Z_scope.
Local Open Scope N_scope.

Let A : Type := Z.
Let B : Type := N.

Context (f : A -> B).
Arguments f _%Z.
Context (f_inj : forall (x y : A) (e : f x = f y), x = y).
Context (f_mono : forall (x y : A) (l : (x <= y)%Z), f x <= f y).
Fail Fail Context (f_surj : forall b : B, exists a : A, b = f a).

(** We implement things in terms of each other.
    Only these really require subtraction,
    decidable equality and some remnant of well-foundedness.
    Everything else can be forced into more general form. *)

Definition unf_down_unf_remdown
  (unf_remdown : B -> A + A * B) `{unf_remdown_spec f unf_remdown}
  (x : B) : A :=
  match unf_remdown x with
  | inl y => y
  | inr (y, z) => y
  end.

Lemma unf_down_unf_remdown_spec
  (unf_remdown : B -> A + A * B) `{unf_remdown_spec f unf_remdown} :
  unf_down_spec f unf_down_unf_remdown.
Proof.
  cbv [unf_down_unf_remdown]. constructor.
  - intros a. rewrite here_remdown. reflexivity.
  - intros x. pose proof refine_remdown x.
    destruct (unf_remdown x) as [a | [a b]] eqn : e.
    + rewrite <- here_remdown in e.
      pose proof f_equal (f_remdown f) e as p.
      repeat rewrite there_remdown in p. rewrite p. split.
      * lia.
      * specialize (@f_mono a (1 + a)%Z ltac:(lia)).
        destruct (N.eqb_spec (f a) (f (1 + a)%Z)).
        specialize (@f_inj a (1 + a)%Z ltac:(assumption)).
        lia. lia.
    + pose proof f_equal (f_remdown f) e as p.
      repeat rewrite there_remdown in p. rewrite p. cbv [f_remdown]. lia. Qed.

Definition unf_error_unf_remdown
  (unf_remdown : B -> A + A * B) `{unf_remdown_spec f unf_remdown}
  (x : B) : option A :=
  match unf_remdown x with
  | inl y => Some y
  | inr (y, z) => None
  end.

Lemma unf_error_unf_remdown_spec
  (unf_remdown : B -> A + A * B) `{unf_remdown_spec f unf_remdown} :
  unf_error_spec f unf_error_unf_remdown.
Proof.
  cbv [unf_error_unf_remdown]. constructor.
  - intros a. rewrite here_remdown. reflexivity.
  - intros x y e'. pose proof refine_remdown x.
    destruct (unf_remdown x) as [a | [a b]] eqn : e.
    + rewrite <- here_remdown in e.
      pose proof f_equal (f_remdown f) e as p.
      repeat rewrite there_remdown in p. rewrite p.
      cbv [option_map] in e'.
      injection e'. clear e'. intros e'. transitivity (f a); auto.
    + inversion e'. Qed.

Definition unf_remdown_unf_down
  (unf_down : B -> A) `{unf_down_spec f unf_down}
  (x : B) : A + A * B :=
  let a := unf_down x in
  let b := x - f a in
  if b =? 0 then inl a else inr (a, b).

Lemma unf_remdown_unf_down_spec
  (unf_down : B -> A) `{unf_down_spec f unf_down} :
  unf_remdown_spec f unf_remdown_unf_down.
Proof.
  cbv [unf_remdown_unf_down]. constructor.
  - intros x. destruct (N.eqb_spec (x - f (unf_down x)) 0) as [e' | f'].
    + constructor.
    + pose proof there_down x as l. lia.
  - intros a. rewrite here_down. rewrite N.sub_diag, N.eqb_refl. reflexivity.
  - intros b. cbv [f_remdown].
    destruct (N.eqb_spec (b - f (unf_down b)) 0) as [e' | f'].
    + pose proof there_down b. lia.
    + lia. Qed.

Definition unf_error_unf_down
  (unf_down : B -> A) `{unf_down_spec f unf_down}
  (b : B) : option A :=
  let a := unf_down b in
  if f a =? b then Some a else None.

Lemma unf_error_unf_down_spec
  (unf_down : B -> A) `{unf_down_spec f unf_down} :
  unf_error_spec f unf_error_unf_down.
Proof.
  cbv [unf_error_unf_down]. constructor.
  - intros a. rewrite here_down. rewrite N.eqb_refl. reflexivity.
  - intros x y e.
    destruct (N.eqb_spec (f (unf_down x)) x) as [e' | f'].
    + cbv [option_map] in e.
      injection e. clear e. intros e. transitivity (f (unf_down x)); auto.
    + inversion e. Qed.

Program Fixpoint unf_remdown_unf_error'
  (unf_down : B -> A) `{unf_down_spec f unf_down}
  (unf_error : B -> option A) `{unf_error_spec f unf_error}
  (y : option B) (x : B)
  {measure (N.to_nat (x - f (unf_down x)))} : A + A * B :=
  match unf_error x with
  | Some a =>
    match y with
    | Some b => inr (a, b)
    | None => inl a
    end
  | None => unf_remdown_unf_error'
    match y with
    | Some b => Some (1 + b)
    | None => Some 1
    end (x - 1)
  end.
Next Obligation.
  intros ? ? ? ? x b g y e.
  enough (b - 1 - f (unf_down (b - 1)) < b - f (unf_down b)) by lia.
  pose proof there_down b as l.
  pose proof there_down (b - 1) as l'.
  destruct (N.eqb_spec b 0) as [e' | f'].
  subst b. replace (0 - 1) with 0 in * by lia. admit.
  apply N.le_succ_l.
  enough (b - f (unf_down (b - 1)) <= b - f (unf_down b)) by lia.
  enough (f (unf_down b) <= f (unf_down (b - 1))) by lia. Admitted.
Next Obligation. Tactics.program_solve_wf. Defined.

Definition unf_remdown_unf_error
  (unf_down : B -> A) `{unf_down_spec f unf_down}
  (unf_error : B -> option A) `{unf_error_spec f unf_error}
  (b : B) : A + A * B :=
  unf_remdown_unf_error' None b.

Lemma unf_remdown_unf_error_spec
  (unf_down : B -> A) `{unf_down_spec f unf_down}
  (unf_error : B -> option A) `{unf_error_spec f unf_error} :
  unf_remdown_spec f unf_remdown_unf_error.
Proof.
  cbv [unf_remdown_unf_error]. constructor.
  - intros x. destruct (unf_remdown_unf_error' None x) as [a | [a b]] eqn : e.
    + constructor.
    + Abort.

Program Fixpoint unf_down_unf_error
  (unf_error : B -> option A) `{unf_error_spec f unf_error}
  (b : B) {measure b (N.le)} : A :=
  match unf_error b with
  | Some a => a
  | None => unf_down_unf_error (b - 1)
  end.
Next Obligation.
  intros ? ? b g x e.
  destruct x as [c |].
  - inversion e.
  - lia. Qed.
Next Obligation. Tactics.program_solve_wf. Admitted.

Lemma unf_down_unf_error_spec
  (unf_error : B -> option A) `{unf_error_spec f unf_error} :
  unf_down_spec f unf_down_unf_error.
Proof.
  constructor.
  - intros a. replace (unf_down_unf_error (f a))
    with match unf_error (f a) with
    | Some a => a
    | None => unf_down_unf_error (f a - 1)
    end by admit. rewrite here_error. reflexivity.
  - intros b. replace (unf_down_unf_error b)
    with match unf_error b with
    | Some a => a
    | None => unf_down_unf_error (b - 1)
    end by admit. induction b using N.peano_ind.
    + destruct (unf_error 0). admit. admit.
    + admit. Abort.

End Context.
