(** * Initialization for all modules. *)

(** We disable warnings about overriding notations,
    because the plan is to replace many basic notations like [<=] and [+]. *)

Global Set Warnings "-notation-overridden".

(** We disable warnings about unsupported attributes,
    because we use some custom attributes as hints. *)

Global Set Warnings "-unsupported-attributes".

(** We turn on automatically inferred implicit arguments and
    make them maximally inserted and conservatively detected,
    since most type classes follow the same design pattern. *)

Global Set Implicit Arguments.
Global Set Maximal Implicit Insertion.
Global Set Strict Implicit.
Global Set Strongly Strict Implicit.
Global Unset Contextual Implicit.
Global Set Reversible Pattern Implicit.

(** We disable universe polymorphism until we really need it,
    because it is experimental and
    incurs a considerable performance penalty on type checking. *)

Global Unset Universe Polymorphism.

(** We do not use implicit generalization,
    because the consequences of accidental misuse
    are worse than the convenience it permits. *)

Global Generalizable No Variables.

(** We use anonymous goals and obligations to define local lemmas,
    which is why we do not want to see them in search results. *)

Add Search Blacklist "Unnamed_".
Add Search Blacklist "_obligation".

(** We export [StrictProp] to be able to
    use strict propositions without ceremony,
    export [Basics] to make their utility functions available everywhere,
    import [Setoid] to generalize the [rewrite] tactic and
    import [PArith], [NArith] and [ZArith] to
    redefine some of the numeral notations. *)

From Coq Require Export
  Logic.StrictProp.
From Coq Require Export
  Program.Basics.
From Coq Require Import
  Setoids.Setoid.
From Coq Require Import
  PArith.PArith NArith.NArith ZArith.ZArith.

(** We export the [rew] notations from [Init.Logic]
    to use them like transport in homotopy type theory. *)

Export EqNotations.

(** We reserve the following notations.
    While doing so is not strictly necessary,
    this list also serves as a quick reference. *)

Reserved Notation "g 'o' f" (at level 40, left associativity).
Reserved Notation "'id'" (at level 0, no associativity).
Reserved Notation "f '^-1'" (at level 25, left associativity).
Reserved Notation "'{' x '$' B '}'" (at level 0, x at level 99).
Reserved Notation "'{' x ':' A '$' B '}'" (at level 0, x at level 99).
Reserved Notation "x '\/' y" (at level 85, right associativity).
Reserved Notation "'_|_'" (at level 0, no associativity).
Reserved Notation "x '/\' y" (at level 80, right associativity).
Reserved Notation "'-|-'" (at level 0, no associativity).
Reserved Notation "x '~~' y" (at level 70, no associativity).
Reserved Notation "x '##' y" (at level 70, no associativity).

(** We can only assert the following notations,
    because they are fixed by the standard library. *)

Reserved Notation "x '<=' y" (at level 70, no associativity).
Reserved Notation "x '+' y" (at level 50, left associativity).
Reserved Notation "'-' x" (at level 35, right associativity).
Reserved Notation "x '-' y" (at level 50, left associativity).
Reserved Notation "x '*' y" (at level 40, left associativity).
Reserved Notation "'/' x" (at level 35, right associativity).
Reserved Notation "x '/' y" (at level 40, left associativity).
Reserved Notation "x '^' y" (at level 30, right associativity).
Reserved Notation "x '==' y" (at level 70, no associativity).
Reserved Notation "x '-->' y" (at level 55, right associativity).
Reserved Notation "'0'" (at level 0, no associativity).
Reserved Notation "'1'" (at level 0, no associativity).

(** These partial applications (operator sections)
    can be generated automatically from the preceding notations. *)

Reserved Notation "'_o_'" (at level 0, no associativity).
Reserved Notation "'_o'_'" (at level 0, no associativity).
Reserved Notation "'_^-1'" (at level 0, no associativity).
Reserved Notation "'{_$_}'" (at level 0, no associativity).
Reserved Notation "'_\/_'" (at level 0, no associativity).
Reserved Notation "'_/\_'" (at level 0, no associativity).
Reserved Notation "'_~~_'" (at level 0, no associativity).
Reserved Notation "'_##_'" (at level 0, no associativity).

Reserved Notation "'_<=_'" (at level 0, no associativity).
Reserved Notation "'_+_'" (at level 0, no associativity).
Reserved Notation "'-_'" (at level 0, no associativity).
Reserved Notation "'_-_'" (at level 0, no associativity).
Reserved Notation "'_*_'" (at level 0, no associativity).
Reserved Notation "'/_'" (at level 0, no associativity).
Reserved Notation "'_/_'" (at level 0, no associativity).
Reserved Notation "'_^_'" (at level 0, no associativity).
Reserved Notation "'_==_'" (at level 0, no associativity).
Reserved Notation "'_-->_'" (at level 0, no associativity).

(** The implicit arguments of [Ssig], [sig] and [sigT] should be the same. *)

Arguments sig {_} _.
Arguments exist {_} _ _ _.
Arguments sigT {_} _.
Arguments existT {_} _ _ _.
Arguments Ssig {_} _.
Arguments Sexists {_} _ _ _.

(** We should have similar notations for [Ssig] as there are for [sig].

    The mnemonic for [$] in the notation is that it is a combination of
    [|] from the notation for [sig] and
    [S] from the name of [Ssig].
    Besides, using [!] would conflict with
    lonely notations of the [Equations] plugin. *)

Notation "'{' x '$' B '}'" := (Ssig (fun x : _ => B)) : type_scope.
Notation "'{' x ':' A '$' B '}'" := (Ssig (fun x : A => B)) : type_scope.

Notation "'{_$_}'" := Ssig (only parsing) : type_scope.

(** Numeral keywords are not a subset of numeral notations,
    which is why we must repeat them here. *)

Notation "'1'" := xH : positive_scope.

Notation "'0'" := O : nat_scope.
Notation "'1'" := (S O) : nat_scope.

Notation "'0'" := N0 : N_scope.
Notation "'1'" := (Npos xH) : N_scope.

Notation "'0'" := Z0 : Z_scope.
Notation "'1'" := (Zpos xH) : Z_scope.

(** We do not allow automatic solution of obligations,
    because we do not want the addition or removal of hints
    to change the total number of obligations. *)

Obligation Tactic := idtac.

(** We might as well allow treating booleans as reflections of propositions. *)

Coercion is_true : bool >-> Sortclass.

(** We define some additional utility functions. *)

(** Currying and uncurrying are swapped around in the standard library,
    which is why we redefine them here. *)

Definition prod_curry (A B C : Type)
  (f : A * B -> C) (a : A) (b : B) : C :=
  f (a, b).

Definition prod_uncurry (A B C : Type)
  (f : A -> B -> C) (x : A * B) : C :=
  f (fst x) (snd x).

Definition prod_curry_dep (A B : Type) (P : A -> B -> Type)
  (f : forall x : A * B, P (fst x) (snd x)) (a : A) (b : B) : P a b :=
  f (a, b).

Definition prod_uncurry_dep (A B : Type) (P : A -> B -> Type)
  (f : forall (a : A) (b : B), P a b) (x : A * B) : P (fst x) (snd x) :=
  f (fst x) (snd x).

Definition sig_curry (A : Type) (P : A -> Prop) (B : Type)
  (f : {a : A | P a} -> B) (a : A) (b : P a) : B :=
  f (exist P a b).

Definition sig_uncurry (A : Type) (P : A -> Prop) (B : Type)
  (f : forall a : A, P a -> B) (x : {a : A | P a}) : B :=
  f (proj1_sig x) (proj2_sig x).

Definition sig_curry_dep
  (A : Type) (P : A -> Prop) (Q : forall a : A, P a -> Type)
  (f : forall x : {a : A | P a}, Q (proj1_sig x) (proj2_sig x))
  (a : A) (b : P a) : Q a b :=
  f (exist P a b).

Definition sig_uncurry_dep
  (A : Type) (P : A -> Prop) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (x : {a : A | P a}) : Q (proj1_sig x) (proj2_sig x) :=
  f (proj1_sig x) (proj2_sig x).

Definition sigT_curry (A : Type) (P : A -> Type) (B : Type)
  (f : {a : A & P a} -> B) (a : A) (b : P a) : B :=
  f (existT P a b).

Definition sigT_uncurry (A : Type) (P : A -> Type) (B : Type)
  (f : forall a : A, P a -> B) (x : {a : A & P a}) : B :=
  f (projT1 x) (projT2 x).

Definition sigT_curry_dep
  (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type)
  (f : forall x : {a : A & P a}, Q (projT1 x) (projT2 x))
  (a : A) (b : P a) : Q a b :=
  f (existT P a b).

Definition sigT_uncurry_dep
  (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (x : {a : A & P a}) : Q (projT1 x) (projT2 x) :=
  f (projT1 x) (projT2 x).

Definition Ssig_curry (A : Type) (P : A -> SProp) (B : Type)
  (f : {a : A $ P a} -> B) (a : A) (b : P a) : B :=
  f (Sexists P a b).

Definition Ssig_uncurry (A : Type) (P : A -> SProp) (B : Type)
  (f : forall a : A, P a -> B) (x : {a : A $ P a}) : B :=
  f (Spr1 x) (Spr2 x).

Definition Ssig_curry_dep
  (A : Type) (P : A -> SProp) (Q : forall a : A, P a -> Type)
  (f : forall x : {a : A $ P a}, Q (Spr1 x) (Spr2 x))
  (a : A) (b : P a) : Q a b :=
  f (Sexists P a b).

Definition Ssig_uncurry_dep
  (A : Type) (P : A -> SProp) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (x : {a : A $ P a}) : Q (Spr1 x) (Spr2 x) :=
  f (Spr1 x) (Spr2 x).

(** Composition, constancy, flipping and application
    are totally fine in the standard library.
    We just augment them with dependent versions. *)

Fail Fail Definition compose (A B C : Type)
  (g : B -> C) (f : A -> B) (a : A) : C :=
  g (f a).

Definition compose_dep
  (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type)
  (g : forall (a : A) (b : P a), Q a b) (f : forall a : A, P a)
  (a : A) : Q a (f a) :=
  g a (f a).

Fail Fail Definition const (A B : Type) (a : A) (b : B) : A := a.

Definition const_dep (A : Type) (P : A -> Type) (a : A) (b : P a) : A := a.

Fail Fail Definition flip (A B C : Type)
  (f : A -> B -> C) (b : B) (a : A) : C := f a b.

Definition flip_dep (A B : Type) (P : A -> B -> Type)
  (f : forall (a : A) (b : B), P a b) (b : B) (a : A) : P a b := f a b.

Fail Fail Definition apply (A B : Type) (f : A -> B) (a : A) : B := f a.

Definition apply_dep (A : Type) (P : A -> Type)
  (f : forall a : A, P a) (a : A) : P a := f a.

(** We mark the utility functions transparent for unification and
    provide some hints for simplifying them.
    Maybe one day there will be a reduction mechanism
    that actually interprets the hints reliably. *)

Typeclasses Transparent Spr1 Spr2.

Typeclasses Transparent andb orb implb xorb negb is_true option_map fst snd
  prod_curry prod_uncurry length app ID Datatypes.id IDProp idProp.

Typeclasses Transparent proj1_sig proj2_sig projT1 projT2
  sig_of_sigT sigT_of_sig.

Typeclasses Transparent compose arrow impl const flip apply.

Typeclasses Transparent prod_curry_dep prod_uncurry_dep
  sig_curry_dep sig_uncurry_dep sig_curry sig_uncurry
  compose_dep const_dep flip_dep apply_dep.

Arguments Spr1 {_ _} !_.
Arguments Spr2 {_ _} !_.

Arguments andb !_ _.
Arguments orb !_ _.
Arguments implb !_ _.
Arguments xorb !_ !_.
Arguments negb !_.
Arguments is_true !_.
Arguments option_map {_ _} _ !_.
Arguments fst {_ _} !_.
Arguments snd {_ _} !_.
Arguments prod_curry {_ _ _} _ _ _ /.
Arguments prod_uncurry {_ _ _} _ !_.
Arguments length {_} !_.
Arguments app {_} !_ _.
Arguments ID /.
Arguments Datatypes.id _ _ /.
Arguments IDProp /.
Arguments idProp _ _ /.

Arguments proj1_sig {_ _} !_.
Arguments proj2_sig {_ _} !_.
Arguments projT1 {_ _} !_.
Arguments projT2 {_ _} !_.
Arguments sig_of_sigT {_ _} !_.
Arguments sigT_of_sig {_ _} !_.

Arguments compose {_ _ _} _ _ _ /.
Arguments arrow _ _ /.
Arguments impl _ _ /.
Arguments const {_ _} _ _ /.
Arguments flip {_ _ _} _ _ _ /.
Arguments apply {_ _} _ _ /.

Arguments prod_curry_dep {_ _ _} _ _ _ /.
Arguments prod_uncurry_dep {_ _ _} _ !_.
Arguments sig_curry {_ _ _} _ _ _ /.
Arguments sig_uncurry {_ _ _} _ !_.
Arguments sig_curry_dep {_ _ _} _ _ _ /.
Arguments sig_uncurry_dep {_ _ _} _ !_.
Arguments sigT_curry {_ _ _} _ _ _ /.
Arguments sigT_uncurry {_ _ _} _ !_.
Arguments sigT_curry_dep {_ _ _} _ _ _ /.
Arguments sigT_uncurry_dep {_ _ _} _ !_.
Arguments Ssig_curry {_ _ _} _ _ _ /.
Arguments Ssig_uncurry {_ _ _} _ !_.
Arguments Ssig_curry_dep {_ _ _} _ _ _ /.
Arguments Ssig_uncurry_dep {_ _ _} _ !_.
Arguments compose_dep {_ _ _} _ _ _ /.
Arguments const_dep {_ _} _ _ /.
Arguments flip_dep {_ _ _} _ _ _ /.
Arguments apply_dep {_ _} _ _ /.

(** Using [o] as a variable name should be prohibited by law,
    which is why we turn it into a notation.
    We also turn [id] into a notation to keep it reusable. *)

Notation "g 'o' f" := (compose g f) : core_scope.
Notation "'id'" := Datatypes.id : core_scope.

Notation "'_o_'" := compose (only parsing) : core_scope.

(** The dependent and nondependent versions are related as follows. *)

Fact eq_prod_curry_nondep (A B C : Type) (f : A * B -> C) (a : A) (b : B) :
  prod_curry_dep f a b = prod_curry f a b.
Proof. reflexivity. Qed.

Fact eq_prod_uncurry_nondep (A B C : Type) (f : A -> B -> C) (x : A * B) :
  prod_uncurry_dep f x = prod_uncurry f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Fact eq_sig_curry_nondep (A : Type) (P : A -> Prop) (B : Type)
  (f : {a : A | P a} -> B) (a : A) (b : P a) :
  sig_curry_dep f a b = sig_curry f a b.
Proof. reflexivity. Qed.

Fact eq_sig_uncurry_nondep (A : Type) (P : A -> Prop) (B : Type)
  (f : forall a : A, P a -> B) (x : {a : A | P a}) :
  sig_uncurry_dep f x = sig_uncurry f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Fact eq_sigT_curry_nondep (A : Type) (P : A -> Type) (B : Type)
  (f : {a : A & P a} -> B) (a : A) (b : P a) :
  sigT_curry_dep f a b = sigT_curry f a b.
Proof. reflexivity. Qed.

Fact eq_sigT_uncurry_nondep (A : Type) (P : A -> Type) (B : Type)
  (f : forall a : A, P a -> B) (x : {a : A & P a}) :
  sigT_uncurry_dep f x = sigT_uncurry f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Fact eq_Ssig_curry_nondep (A : Type) (P : A -> SProp) (B : Type)
  (f : {a : A $ P a} -> B) (a : A) (b : P a) :
  Ssig_curry_dep f a b = Ssig_curry f a b.
Proof. reflexivity. Qed.

Fact eq_Ssig_uncurry_nondep (A : Type) (P : A -> SProp) (B : Type)
  (f : forall a : A, P a -> B) (x : {a : A $ P a}) :
  Ssig_uncurry_dep f x = Ssig_uncurry f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Fact eq_compose_nondep (A B C : Type) (g : B -> C) (f : A -> B) (a : A) :
  compose_dep (const g) f a = compose g f a.
Proof. reflexivity. Qed.

Fact eq_const_nondep (A B : Type) (a : A) (b : B) :
  const_dep a b = const a b.
Proof. reflexivity. Qed.

Fact eq_flip_nondep (A B C : Type) (f : A -> B -> C) (b : B) (a : A) :
  flip_dep f b a = flip f b a.
Proof. reflexivity. Qed.

Fact eq_apply_nondep (A B : Type) (f : A -> B) (a : A) :
  apply_dep f a = apply f a.
Proof. reflexivity. Qed.

(** Some other properties also hold. *)

Lemma eq_prod_uncurry_curry (A B : Type) (P : A -> B -> Type)
  (f : forall x : A * B, P (fst x) (snd x)) (x : A * B) :
  prod_uncurry_dep (prod_curry_dep f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_prod_curry_uncurry (A B : Type) (P : A -> B -> Type)
  (f : forall (a : A) (b : B), P a b) (a : A) (b : B) :
  prod_curry_dep (prod_uncurry_dep f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_sig_uncurry_curry
  (A : Type) (P : A -> Prop) (Q : forall a : A, P a -> Type)
  (f : forall x : {a : A | P a}, Q (proj1_sig x) (proj2_sig x))
  (x : {a : A | P a}) :
  sig_uncurry_dep (sig_curry_dep f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_sig_curry_uncurry
  (A : Type) (P : A -> Prop) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (a : A) (b : P a) :
  sig_curry_dep (sig_uncurry_dep f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_sigT_uncurry_curry
  (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type)
  (f : forall x : {a : A & P a}, Q (projT1 x) (projT2 x))
  (x : {a : A & P a}) :
  sigT_uncurry_dep (sigT_curry_dep f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_sigT_curry_uncurry
  (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (a : A) (b : P a) :
  sigT_curry_dep (sigT_uncurry_dep f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_Ssig_uncurry_curry
  (A : Type) (P : A -> SProp) (Q : forall a : A, P a -> Type)
  (f : forall x : {a : A $ P a}, Q (Spr1 x) (Spr2 x))
  (x : {a : A $ P a}) :
  Ssig_uncurry_dep (Ssig_curry_dep f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_Ssig_curry_uncurry
  (A : Type) (P : A -> SProp) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (a : A) (b : P a) :
  Ssig_curry_dep (Ssig_uncurry_dep f) a b = f a b.
Proof. reflexivity. Qed.

Lemma compose_assoc (A B C D : Type)
  (h : C -> D) (g : B -> C) (f : A -> B) (a : A) :
  compose h (compose g f) a = compose (compose h g) f a.
Proof. reflexivity. Qed.

Lemma compose_dep_assoc
  (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type)
  (R : forall (a : A) (b : P a), Q a b -> Type)
  (h : forall (a : A) (b : P a) (z : Q a b), R a b z)
  (g : forall (a : A) (b : P a), Q a b) (f : forall a : A, P a) (a : A) :
  compose_dep (fun a : A => h a (f a)) (compose_dep g f) a =
  compose_dep (fun a : A => compose_dep (h a) (g a)) f a.
Proof. reflexivity. Qed.

Lemma flip_involutive (A B C : Type)
  (f : A -> B -> C) (a : A) (b : B) :
  flip (flip f) a b = f a b.
Proof. reflexivity. Qed.

Lemma flip_dep_involutive (A B : Type) (P : A -> B -> Type)
  (f : forall (a : A) (b : B), P a b) (b : B) (a : A) :
  flip_dep (flip_dep f) a b = f a b.
Proof. reflexivity. Qed.

(** We define the following tactic notations
    to conveniently specialize superclasses into subclasses.
    There are more principled ways to do this,
    but they all require plugins or other more advanced mechanisms.
    Besides, eight arguments ought to be enough for anybody. *)

Tactic Notation "typeclasses"
  tactic3(xy0) :=
  xy0 || fail "Failed to specialize".

Tactic Notation "typeclasses"
  tactic3(xy0) "or" tactic3(xy1) :=
  xy0 || xy1 || fail "Failed to specialize".

Tactic Notation "typeclasses"
  tactic3(xy0) "or" tactic3(xy1) "or"
  tactic3(xy2) :=
  xy0 || xy1 ||
  xy2 || fail "Failed to specialize".

Tactic Notation "typeclasses"
  tactic3(xy0) "or" tactic3(xy1) "or"
  tactic3(xy2) "or" tactic3(xy3) :=
  xy0 || xy1 ||
  xy2 || xy3 || fail "Failed to specialize".

Tactic Notation "typeclasses"
  tactic3(xy0) "or" tactic3(xy1) "or"
  tactic3(xy2) "or" tactic3(xy3) "or"
  tactic3(xy4) :=
  xy0 || xy1 ||
  xy2 || xy3 ||
  xy4 || fail "Failed to specialize".

Tactic Notation "typeclasses"
  tactic3(xy0) "or" tactic3(xy1) "or"
  tactic3(xy2) "or" tactic3(xy3) "or"
  tactic3(xy4) "or" tactic3(xy5) :=
  xy0 || xy1 ||
  xy2 || xy3 ||
  xy4 || xy5 || fail "Failed to specialize".

Tactic Notation "typeclasses"
  tactic3(xy0) "or" tactic3(xy1) "or"
  tactic3(xy2) "or" tactic3(xy3) "or"
  tactic3(xy4) "or" tactic3(xy5) "or"
  tactic3(xy6) :=
  xy0 || xy1 ||
  xy2 || xy3 ||
  xy4 || xy5 ||
  xy6 || fail "Failed to specialize".

Tactic Notation "typeclasses"
  tactic3(xy0) "or" tactic3(xy1) "or"
  tactic3(xy2) "or" tactic3(xy3) "or"
  tactic3(xy4) "or" tactic3(xy5) "or"
  tactic3(xy6) "or" tactic3(xy7) :=
  xy0 || xy1 ||
  xy2 || xy3 ||
  xy4 || xy5 ||
  xy6 || xy7 || fail "Failed to specialize".

Tactic Notation "convert"
  uconstr(x0) "into" uconstr(y0) :=
  change x0 with y0 in *.

Tactic Notation "convert"
  uconstr(x0) "into" uconstr(y0) "and" uconstr(x1) "into" uconstr(y1) :=
  change x0 with y0 in *; change x1 with y1 in *.

Tactic Notation "convert"
  uconstr(x0) "into" uconstr(y0) "and" uconstr(x1) "into" uconstr(y1) "and"
  uconstr(x2) "into" uconstr(y2) :=
  change x0 with y0 in *; change x1 with y1 in *;
  change x2 with y2 in *.

Tactic Notation "convert"
  uconstr(x0) "into" uconstr(y0) "and" uconstr(x1) "into" uconstr(y1) "and"
  uconstr(x2) "into" uconstr(y2) "and" uconstr(x3) "into" uconstr(y3) :=
  change x0 with y0 in *; change x1 with y1 in *;
  change x2 with y2 in *; change x3 with y3 in *.

Tactic Notation "convert"
  uconstr(x0) "into" uconstr(y0) "and" uconstr(x1) "into" uconstr(y1) "and"
  uconstr(x2) "into" uconstr(y2) "and" uconstr(x3) "into" uconstr(y3) "and"
  uconstr(x4) "into" uconstr(y4) :=
  change x0 with y0 in *; change x1 with y1 in *;
  change x2 with y2 in *; change x3 with y3 in *;
  change x4 with y4 in *.

Tactic Notation "convert"
  uconstr(x0) "into" uconstr(y0) "and" uconstr(x1) "into" uconstr(y1) "and"
  uconstr(x2) "into" uconstr(y2) "and" uconstr(x3) "into" uconstr(y3) "and"
  uconstr(x4) "into" uconstr(y4) "and" uconstr(x5) "into" uconstr(y5) :=
  change x0 with y0 in *; change x1 with y1 in *;
  change x2 with y2 in *; change x3 with y3 in *;
  change x4 with y4 in *; change x5 with y5 in *.

Tactic Notation "convert"
  uconstr(x0) "into" uconstr(y0) "and" uconstr(x1) "into" uconstr(y1) "and"
  uconstr(x2) "into" uconstr(y2) "and" uconstr(x3) "into" uconstr(y3) "and"
  uconstr(x4) "into" uconstr(y4) "and" uconstr(x5) "into" uconstr(y5) "and"
  uconstr(x6) "into" uconstr(y6) :=
  change x0 with y0 in *; change x1 with y1 in *;
  change x2 with y2 in *; change x3 with y3 in *;
  change x4 with y4 in *; change x5 with y5 in *;
  change x6 with y6 in *.

Tactic Notation "convert"
  uconstr(x0) "into" uconstr(y0) "and" uconstr(x1) "into" uconstr(y1) "and"
  uconstr(x2) "into" uconstr(y2) "and" uconstr(x3) "into" uconstr(y3) "and"
  uconstr(x4) "into" uconstr(y4) "and" uconstr(x5) "into" uconstr(y5) "and"
  uconstr(x6) "into" uconstr(y6) "and" uconstr(x7) "into" uconstr(y7) :=
  change x0 with y0 in *; change x1 with y1 in *;
  change x2 with y2 in *; change x3 with y3 in *;
  change x4 with y4 in *; change x5 with y5 in *;
  change x6 with y6 in *; change x7 with y7 in *.
