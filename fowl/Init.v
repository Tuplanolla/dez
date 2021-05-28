(** * Initialization for All Libraries *)

(** We export [StrictProp] to be able
    to use strict propositions without ceremony,
    export [Basics] and [Relations]
    to make their utility functions available everywhere,
    export [Morphisms] and [RelationClasses]
    to build a symbiotic relationship with the standard library,
    import [PArith], [NArith], [ZArith], [QArith], [Reals],
    [Int31] and [Int63] in order
    to redefine some of the basic numeral notations,
    import [List] to manually define some corollaries
    that would otherwise be automatically generated and
    export [Equations] as we make heavy use of the equations plugin.
    All of the imports and exports are carried out before setting options,
    because we want to ensure that the options we set are not overridden
    by other libraries. *)

From Coq Require Export
  Logic.StrictProp.
From Coq Require Export
  Program.Basics Program.Tactics Relations.Relations.
From Coq Require Export
  Classes.Morphisms Classes.RelationClasses.
From Coq Require Import
  PArith.PArith NArith.NArith ZArith.ZArith QArith.QArith Reals.Reals
  Numbers.Cyclic.Int31.Int31 Numbers.Cyclic.Int63.Int63.
From Coq Require Import
  Lists.List.
From Equations.Prop Require Export
  Equations.

(** We disable warnings about unsupported attributes,
    because we use some custom attributes as refactoring hints. *)

#[global] Set Warnings "-unsupported-attributes".

(** We disable warnings about overriding notations,
    because we overload many standard library notations
    with operational type classes. *)

#[global] Set Warnings "-notation-overridden".

(** We turn on automatically inferred implicit arguments and
    make them maximally inserted and conservatively detected,
    since most type classes follow the same design pattern. *)

#[global] Set Implicit Arguments.
#[global] Set Maximal Implicit Insertion.
#[global] Set Strict Implicit.
#[global] Set Strongly Strict Implicit.
#[global] Unset Contextual Implicit.
#[global] Set Reversible Pattern Implicit.

(** We need to enable universe polymorphism
    for unification of strict propositions,
    even though the feature is experimental and
    incurs a considerable performance penalty on type checking. *)

#[global] Set Universe Polymorphism.

(** We mark equations transparent,
    because it may be necessary to [unfold] them manually
    when [simp] would either fail to progress or diverge. *)

#[global] Set Equations Transparent.

(** We do not allow automatic solution of obligations,
    because we do not want the addition or removal of hints
    to change the total number of obligations.

    The default tactic is
    [program_simplify;
    try typeclasses eauto 10 with program;
    try program_solve_wf]. *)

Obligation Tactic := try program_solve_wf.

(** We do not use implicit generalization,
    because the consequences of accidental misuse
    are worse than the convenience it permits. *)

#[global] Generalizable No Variables.

(** We use anonymous goals and obligations to define local lemmas,
    which is why we do not want to see them in search results. *)

Add Search Blacklist "Unnamed_".
Add Search Blacklist "_obligation".

(** We do not want to see obvious instances generated
    by the equations plugin either. *)

Add Search Blacklist "FunctionalElimination_".
Add Search Blacklist "FunctionalInduction_".

(** We reserve the following notations.
    While doing so is not strictly necessary,
    this list also serves as a quick reference. *)

Reserved Notation "'{' x '$' B '}'" (at level 0, x at level 99).
Reserved Notation "'{' x ':' A '$' B '}'" (at level 0, x at level 99).

Reserved Notation "R '<==' S" (right associativity, at level 55).
Reserved Notation "R '<--' S" (right associativity, at level 55).
Reserved Notation "R '<==>' S" (right associativity, at level 55).
Reserved Notation "R '<-->' S" (right associativity, at level 55).

Reserved Notation "'0'" (no associativity, at level 0).
Reserved Notation "'1'" (no associativity, at level 0).

Reserved Notation "g 'o' f" (left associativity, at level 40).
Reserved Notation "'id'" (no associativity, at level 0).
Reserved Notation "f '^-1'" (left associativity, at level 25).
Reserved Notation "x '~~' y" (no associativity, at level 70).
Reserved Notation "x '##' y" (no associativity, at level 70).

(** We can only assert the following notations,
    because they are fixed by the standard library. *)

Reserved Notation "R '==>' S" (right associativity, at level 55).
Reserved Notation "R '-->' S" (right associativity, at level 55).

Reserved Notation "x '=' y" (no associativity, at level 70).
Reserved Notation "x '==' y" (no associativity, at level 70).
Reserved Notation "x '===' y" (no associativity, at level 70).

Reserved Notation "x '\/' y" (right associativity, at level 85).
Reserved Notation "x '/\' y" (right associativity, at level 80).
Reserved Notation "y '<=' x" (no associativity, at level 70).
Reserved Notation "x '+' y" (left associativity, at level 50).
Reserved Notation "'-' x" (right associativity, at level 35).
Reserved Notation "y '-' x" (left associativity, at level 50).
Reserved Notation "x '*' y" (left associativity, at level 40).
Reserved Notation "'/' x" (right associativity, at level 35).
Reserved Notation "y '/' x" (left associativity, at level 40).
Reserved Notation "y '^' x" (right associativity, at level 30).

(** These partial applications (operator sections)
    could be generated automatically from the preceding notations. *)

Reserved Notation "'{_$_}'" (no associativity, at level 0).
Reserved Notation "'{_:_$_}'" (no associativity, at level 0).

Reserved Notation "'_<==_'" (no associativity, at level 0).
Reserved Notation "'_<--_'" (no associativity, at level 0).
Reserved Notation "'_<==>_'" (no associativity, at level 0).
Reserved Notation "'_<-->_'" (no associativity, at level 0).

Reserved Notation "'_o_'" (no associativity, at level 0).
Reserved Notation "'_^-1'" (no associativity, at level 0).
Reserved Notation "'_~~_'" (no associativity, at level 0).
Reserved Notation "'_##_'" (no associativity, at level 0).

Reserved Notation "'_==>_'" (no associativity, at level 0).
Reserved Notation "'_-->_'" (no associativity, at level 0).

Reserved Notation "'_=_'" (no associativity, at level 0).
Reserved Notation "'_==_'" (no associativity, at level 0).
Reserved Notation "'_===_'" (no associativity, at level 0).

Reserved Notation "'_\/_'" (no associativity, at level 0).
Reserved Notation "'_/\_'" (no associativity, at level 0).
Reserved Notation "'_<=_'" (no associativity, at level 0).
Reserved Notation "'_+_'" (no associativity, at level 0).
Reserved Notation "'-_'" (no associativity, at level 0).
Reserved Notation "'_-_'" (no associativity, at level 0).
Reserved Notation "'_*_'" (no associativity, at level 0).
Reserved Notation "'/_'" (no associativity, at level 0).
Reserved Notation "'_/_'" (no associativity, at level 0).
Reserved Notation "'_^_'" (no associativity, at level 0).

(** The implicit arguments of [Ssig], [sig] and [sigT] should be the same. *)

Arguments sig {_} _.
Arguments exist {_} _ _ _.
Arguments sigT {_} _.
Arguments existT {_} _ _ _.
Arguments Ssig {_} _.
Arguments Sexists {_} _ _ _.

(** We should have similar notations for [Ssig] as there are for [sig].
    The mnemonic for [$] in the notation is that it is a combination
    of [|] from the notation for [sig] and [S] from the name of [Ssig].
    Besides, using [!] would conflict with
    the lonely notations of the equations plugin. *)

Notation "'{' x '$' B '}'" := (Ssig (fun x : _ => B)) : type_scope.
Notation "'{' x ':' A '$' B '}'" := (@Ssig A (fun x : _ => B)) : type_scope.

Notation "'{_$_}'" := Ssig (only parsing) : type_scope.
Notation "'{_:_$_}'" := @Ssig (only parsing) : type_scope.

(** Using [o] as a variable name should be prohibited by law,
    which is why we turn it into a notation instead.
    We also turn [id] into a notation to keep it reusable. *)

Notation "g 'o' f" := (compose g f) : core_scope.
Notation "'id'" := Datatypes.id : core_scope.

Notation "'_o_'" := compose (only parsing) : core_scope.

(** We export the [rew] notations from [Init.Logic]
    to use them like transport in homotopy type theory. *)

Export EqNotations.

(** We might as well treat booleans as reflections of propositions. *)

Coercion is_true : bool >-> Sortclass.

(** Respectful morphisms have an obvious dual
    that is missing from the standard library. *)

#[global] Open Scope signature_scope.

Fail Fail Definition respectful (A B : Type)
  (R : relation A) (S : relation B) : relation (A -> B) :=
  fun f g : A -> B =>
  forall x y : A, R x y -> S (f x) (g y).

Fail Fail Notation "R '==>' S" := (respectful R S) : signature_scope.

Definition corespectful (A B : Type)
  (R : relation B) (S : relation A) : relation (A -> B) :=
  fun f g : A -> B =>
  forall x y : A, R (f x) (g y) -> S x y.

Notation "R '<==' S" := (corespectful R S) : signature_scope.

Definition birespectful (A B C : Type)
  (R : relation B) (S : relation C) : relation ((A -> B) * (A -> C)) :=
  fun fh gk : (A -> B) * (A -> C) =>
  forall x y : A, R (fst fh x) (fst gk y) -> S (snd fh x) (snd gk y).

Notation "R '<==>' S" := (birespectful R S) : signature_scope.

Typeclasses Opaque respectful corespectful birespectful.

(** Numeral keywords are not a subset of numeral notations,
    which is why we must repeat them here. *)

Notation "'0'" := False : type_scope.
Notation "'1'" := True : type_scope.

Notation "'1'" := xH : positive_scope.

Notation "'0'" := O : nat_scope.
Notation "'0'" := O : hex_nat_scope.
Notation "'1'" := (S O) : nat_scope.
Notation "'1'" := (S O) : hex_nat_scope.

Notation "'0'" := N0 : N_scope.
Notation "'1'" := (Npos xH) : N_scope.

Notation "'0'" := Z0 : Z_scope.
Notation "'1'" := (Zpos xH) : Z_scope.

Module Decimal.

Export Coq.Init.Decimal.

Notation "'0'" := (D0 Nil) : dec_uint_scope.
Notation "'1'" := (D1 Nil) : dec_uint_scope.

Notation "'0'" := (Pos (D0 Nil)) : dec_int_scope.
Notation "'1'" := (Pos (D1 Nil)) : dec_int_scope.

End Decimal.

Module Hexadecimal.

Export Coq.Init.Hexadecimal.

Notation "'0'" := (D0 Nil) : dec_uint_scope.
Notation "'1'" := (D1 Nil) : dec_uint_scope.

Notation "'0'" := (Pos (D0 Nil)) : dec_int_scope.
Notation "'1'" := (Pos (D1 Nil)) : dec_int_scope.

End Hexadecimal.

(** We would rather not touch primitive integers,
    because they are strange and fragile. *)

Notation "'0'" := On : int31_scope.
Notation "'1'" := In : int31_scope.

(* Notation "'0'" := _ : int63_scope.
Notation "'1'" := _ : int63_scope. *)

Notation "'0'" := (Qmake Z0 xH) : hex_Q_scope.
Notation "'0'" := (Qmake Z0 xH) : Q_scope.
Notation "'1'" := (Qmake (Zpos xH) xH) : hex_Q_scope.
Notation "'1'" := (Qmake (Zpos xH) xH) : Q_scope.

Notation "'0'" := R0 : hex_R_scope.
Notation "'0'" := R0 : R_scope.
Notation "'1'" := R1 : hex_R_scope.
Notation "'1'" := R1 : R_scope.

(** We define some additional utility functions. *)

(** Currying and uncurrying are swapped around in the standard library,
    which is why we redefine them here. *)

Equations prod_curry (A B C : Type)
  (f : A * B -> C) (a : A) (b : B) : C :=
  prod_curry f a b := f (a, b).

Equations prod_uncurry (A B C : Type)
  (f : A -> B -> C) (x : A * B) : C :=
  prod_uncurry f x := f (fst x) (snd x).

Equations prod_curry_dep (A B : Type) (P : A -> B -> Type)
  (f : forall x : A * B, P (fst x) (snd x)) (a : A) (b : B) : P a b :=
  prod_curry_dep _ f a b := f (a, b).

Equations prod_uncurry_dep (A B : Type) (P : A -> B -> Type)
  (f : forall (a : A) (b : B), P a b) (x : A * B) : P (fst x) (snd x) :=
  prod_uncurry_dep f x := f (fst x) (snd x).

Equations sig_curry (A : Type) (P : A -> Prop) (B : Type)
  (f : {a : A | P a} -> B) (a : A) (b : P a) : B :=
  sig_curry f a b := f (exist P a b).

Equations sig_uncurry (A : Type) (P : A -> Prop) (B : Type)
  (f : forall a : A, P a -> B) (x : {a : A | P a}) : B :=
  sig_uncurry f x := f (proj1_sig x) (proj2_sig x).

Equations sig_curry_dep
  (A : Type) (P : A -> Prop) (Q : forall a : A, P a -> Type)
  (f : forall x : {a : A | P a}, Q (proj1_sig x) (proj2_sig x))
  (a : A) (b : P a) : Q a b :=
  sig_curry_dep _ f a b := f (exist P a b).

Equations sig_uncurry_dep
  (A : Type) (P : A -> Prop) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (x : {a : A | P a}) : Q (proj1_sig x) (proj2_sig x) :=
  sig_uncurry_dep f x := f (proj1_sig x) (proj2_sig x).

Equations sigT_curry (A : Type) (P : A -> Type) (B : Type)
  (f : {a : A & P a} -> B) (a : A) (b : P a) : B :=
  sigT_curry f a b := f (existT P a b).

Equations sigT_uncurry (A : Type) (P : A -> Type) (B : Type)
  (f : forall a : A, P a -> B) (x : {a : A & P a}) : B :=
  sigT_uncurry f x := f (projT1 x) (projT2 x).

Equations sigT_curry_dep
  (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type)
  (f : forall x : {a : A & P a}, Q (projT1 x) (projT2 x))
  (a : A) (b : P a) : Q a b :=
  sigT_curry_dep _ f a b := f (existT P a b).

Equations sigT_uncurry_dep
  (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (x : {a : A & P a}) : Q (projT1 x) (projT2 x) :=
  sigT_uncurry_dep f x := f (projT1 x) (projT2 x).

Equations Ssig_curry (A : Type) (P : A -> SProp) (B : Type)
  (f : {a : A $ P a} -> B) (a : A) (b : P a) : B :=
  Ssig_curry f a b := f (Sexists P a b).

Equations Ssig_uncurry (A : Type) (P : A -> SProp) (B : Type)
  (f : forall a : A, P a -> B) (x : {a : A $ P a}) : B :=
  Ssig_uncurry f x := f (Spr1 x) (Spr2 x).

Equations Ssig_curry_dep
  (A : Type) (P : A -> SProp) (Q : forall a : A, P a -> Type)
  (f : forall x : {a : A $ P a}, Q (Spr1 x) (Spr2 x))
  (a : A) (b : P a) : Q a b :=
  Ssig_curry_dep _ f a b := f (Sexists P a b).

Equations Ssig_uncurry_dep
  (A : Type) (P : A -> SProp) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (x : {a : A $ P a}) : Q (Spr1 x) (Spr2 x) :=
  Ssig_uncurry_dep f x := f (Spr1 x) (Spr2 x).

Equations conj_curry (A B C : Prop)
  (f : A /\ B -> C) (a : A) (b : B) : C :=
  conj_curry f a b := f (conj a b).

Equations conj_uncurry (A B C : Prop)
  (f : A -> B -> C) (x : A /\ B) : C :=
  conj_uncurry f x := f (proj1 x) (proj2 x).

(** Composition, constancy, flipping and application
    are totally fine in the standard library.
    We just accompany them with dependent versions. *)

Fail Fail Equations compose (A B C : Type)
  (g : B -> C) (f : A -> B) (a : A) : C :=
  compose g f a := g (f a).

Corollary compose_equation_1 (A B C : Type)
  (g : B -> C) (f : A -> B) (x : A) : (g o f) x = g (f x).
Proof. reflexivity. Qed.

Hint Rewrite @compose_equation_1 : compose.

Equations compose_dep
  (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type)
  (g : forall (a : A) (b : P a), Q a b) (f : forall a : A, P a)
  (a : A) : Q a (f a) :=
  compose_dep g f a := g a (f a).

Fail Fail Equations arrow (A B : Type) : Type :=
  arrow A B := A -> B.

Corollary arrow_equation_1 (A B : Type) : arrow A B = (A -> B).
Proof. reflexivity. Qed.

Hint Rewrite @arrow_equation_1 : arrow.

Fail Fail Equations impl (A B : Prop) : Prop :=
  impl A B := A -> B.

Corollary impl_equation_1 (A B : Prop) : impl A B = (A -> B).
Proof. reflexivity. Qed.

Hint Rewrite @impl_equation_1 : impl.

Fail Fail Equations const (A B : Type) (a : A) (b : B) : A :=
  const a b := a.

Corollary const_equation_1 (A B : Type) (a : A) (b : B) : const a b = a.
Proof. reflexivity. Qed.

Hint Rewrite @const_equation_1 : const.

Equations const_dep (A : Type) (P : A -> Type) (a : A) (b : P a) : A :=
  const_dep _ a b := a.

Fail Fail Equations flip (A B C : Type)
  (f : A -> B -> C) (b : B) (a : A) : C :=
  flip f b a := f a b.

Corollary flip_equation_1 (A B C : Type) (f : A -> B -> C) (x : B) (y : A) :
  flip f x y = f y x.
Proof. reflexivity. Qed.

Hint Rewrite @flip_equation_1 : flip.

Equations flip_dep (A B : Type) (P : A -> B -> Type)
  (f : forall (a : A) (b : B), P a b) (b : B) (a : A) : P a b :=
  flip_dep f b a := f a b.

Fail Fail Equations apply (A B : Type) (f : A -> B) (a : A) : B :=
  apply f a := f a.

Corollary apply_equation_1 (A B : Type) (f : A -> B) (x : A) :
  apply f x = f x.
Proof. reflexivity. Qed.

Hint Rewrite @apply_equation_1 : apply.

Equations apply_dep (A : Type) (P : A -> Type)
  (f : forall a : A, P a) (a : A) : P a :=
  apply_dep f a := f a.

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
Arguments Datatypes.id {_} _ /.
Arguments IDProp /.
Arguments idProp {_} _ /.

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
Arguments conj_curry {_ _ _} _ _ _ /.
Arguments conj_uncurry {_ _ _} _ !_.
Arguments compose_dep {_ _ _} _ _ _ /.
Arguments const_dep {_ _} _ _ /.
Arguments flip_dep {_ _ _} _ _ _ /.
Arguments apply_dep {_ _} _ _ /.

(** This is another way to state [Spr1_inj]
    without breaking unification when universe polymorphism is turned off. *)

Lemma eq_Ssig (A : Type) (P : A -> SProp)
  (a0 : A) (b0 : P a0) (a1 : A) (b1 : P a1)
  (e : a0 = a1) : Sexists P a0 b0 = Sexists P a1 b1.
Proof. apply Spr1_inj. auto. Qed.

(** The dependent and nondependent versions are related as follows. *)

Lemma eq_prod_curry_nondep (A B C : Type) (f : A * B -> C) (a : A) (b : B) :
  prod_curry_dep f a b = prod_curry f a b.
Proof. reflexivity. Qed.

Lemma eq_prod_uncurry_nondep (A B C : Type) (f : A -> B -> C) (x : A * B) :
  prod_uncurry_dep f x = prod_uncurry f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_sig_curry_nondep (A : Type) (P : A -> Prop) (B : Type)
  (f : {a : A | P a} -> B) (a : A) (b : P a) :
  sig_curry_dep f a b = sig_curry f a b.
Proof. reflexivity. Qed.

Lemma eq_sig_uncurry_nondep (A : Type) (P : A -> Prop) (B : Type)
  (f : forall a : A, P a -> B) (x : {a : A | P a}) :
  sig_uncurry_dep f x = sig_uncurry f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_sigT_curry_nondep (A : Type) (P : A -> Type) (B : Type)
  (f : {a : A & P a} -> B) (a : A) (b : P a) :
  sigT_curry_dep f a b = sigT_curry f a b.
Proof. reflexivity. Qed.

Lemma eq_sigT_uncurry_nondep (A : Type) (P : A -> Type) (B : Type)
  (f : forall a : A, P a -> B) (x : {a : A & P a}) :
  sigT_uncurry_dep f x = sigT_uncurry f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_Ssig_curry_nondep (A : Type) (P : A -> SProp) (B : Type)
  (f : {a : A $ P a} -> B) (a : A) (b : P a) :
  Ssig_curry_dep f a b = Ssig_curry f a b.
Proof. reflexivity. Qed.

Lemma eq_Ssig_uncurry_nondep (A : Type) (P : A -> SProp) (B : Type)
  (f : forall a : A, P a -> B) (x : {a : A $ P a}) :
  Ssig_uncurry_dep f x = Ssig_uncurry f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_compose_nondep (A B C : Type) (g : B -> C) (f : A -> B) (a : A) :
  compose_dep (const g) f a = compose g f a.
Proof. reflexivity. Qed.

Lemma eq_const_nondep (A B : Type) (a : A) (b : B) :
  const_dep a b = const a b.
Proof. reflexivity. Qed.

Lemma eq_flip_nondep (A B C : Type) (f : A -> B -> C) (b : B) (a : A) :
  flip_dep f b a = flip f b a.
Proof. reflexivity. Qed.

Lemma eq_apply_nondep (A B : Type) (f : A -> B) (a : A) :
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

(** This incomplete set of corollaries
    would be generated by equations plugin. *)

Import ListNotations.

#[local] Open Scope bool_scope.

Section Context.

#[local] Set Cumulative StrictProp.

Corollary Spr1_equation_1 (A : Type) (P : A -> SProp) (a : A) (b : P a) :
  Spr1 (Sexists P a b) = a.
Proof. reflexivity. Qed.

Corollary Spr2_equation_1 (A : Type) (P : A -> SProp) (a : A) (b : P a) :
  Spr2 (Sexists P a b) = b.
Proof. reflexivity. Qed.

End Context.

Hint Rewrite @Spr1_equation_1 : Spr1.

Hint Rewrite @Spr2_equation_1 : Spr2.

Corollary andb_equation_1 (b1 b2 : bool) :
  true && b2 = b2.
Proof. reflexivity. Qed.

Corollary andb_equation_2 (b1 b2 : bool) :
  false && b2 = false.
Proof. reflexivity. Qed.

Hint Rewrite @andb_equation_1 @andb_equation_2 : andb.

Corollary orb_equation_1 (b1 b2 : bool) :
  true || b2 = true.
Proof. reflexivity. Qed.

Corollary orb_equation_2 (b1 b2 : bool) :
  false || b2 = b2.
Proof. reflexivity. Qed.

Hint Rewrite @orb_equation_1 @orb_equation_2 : orb.

Corollary implb_equation_1 (b1 b2 : bool) :
  implb true b2 = b2.
Proof. reflexivity. Qed.

Corollary implb_equation_2 (b1 b2 : bool) :
  implb false b2 = true.
Proof. reflexivity. Qed.

Hint Rewrite @implb_equation_1 @implb_equation_2 : implb.

Corollary xorb_equation_1 (b1 b2 : bool) :
  xorb true true = false.
Proof. reflexivity. Qed.

Corollary xorb_equation_2 (b1 b2 : bool) :
  xorb true false = true.
Proof. reflexivity. Qed.

Corollary xorb_equation_3 (b1 b2 : bool) :
  xorb false true = true.
Proof. reflexivity. Qed.

Corollary xorb_equation_4 (b1 b2 : bool) :
  xorb false false = false.
Proof. reflexivity. Qed.

Hint Rewrite @xorb_equation_1 @xorb_equation_2
  @xorb_equation_3 @xorb_equation_4 : xorb.

Corollary negb_equation_1 (b : bool) :
  negb true = false.
Proof. reflexivity. Qed.

Corollary negb_equation_2 (b : bool) :
  negb false = true.
Proof. reflexivity. Qed.

Hint Rewrite @negb_equation_1 @negb_equation_2 : negb.

Corollary is_true_equation_1 (b : bool) :
  is_true b = (b = true).
Proof. reflexivity. Qed.

Hint Rewrite @is_true_equation_1 : is_true.

Corollary option_map_equation_1 (A B : Type) (f : A -> B) (a : A) :
  option_map f (Some a) = Some (f a).
Proof. reflexivity. Qed.

Corollary option_map_equation_2 (A B : Type) (f : A -> B) :
  option_map f None = None.
Proof. reflexivity. Qed.

Hint Rewrite @option_map_equation_1 @option_map_equation_2 : option_map.

Corollary fst_equation_1 (A B : Type) (x : A) (y : B) : fst (x, y) = x.
Proof. reflexivity. Qed.

Hint Rewrite @fst_equation_1 : fst.

Corollary snd_equation_1 (A B : Type) (x : A) (y : B) : snd (x, y) = y.
Proof. reflexivity. Qed.

Hint Rewrite @snd_equation_1 : snd.

Corollary length_equation_1 (A : Type) :
  length (A := A) [] = O.
Proof. reflexivity. Qed.

Corollary length_equation_2 (A : Type) (a : A) (l' : list A) :
  length (a :: l') = S (length l').
Proof. reflexivity. Qed.

Hint Rewrite @length_equation_1 @length_equation_2 : length.

Corollary app_equation_1 (A : Type) (m : list A) :
  [] ++ m = m.
Proof. reflexivity. Qed.

Corollary app_equation_2 (A : Type) (a : A) (l1 m : list A) :
  (a :: l1) ++ m = a :: (l1 ++ m).
Proof. reflexivity. Qed.

Hint Rewrite @app_equation_1 @app_equation_2 : app.

Corollary ID_equation_1 : ID = forall A : Type, A -> A.
Proof. reflexivity. Qed.

Hint Rewrite @ID_equation_1 : ID.

Corollary id_equation_1 (A : Type) (x : A) : id x = x.
Proof. reflexivity. Qed.

(** We cannot refer to the [id] hint database,
    because we use it as a keyword in a notation. *)

(* Fail Hint Rewrite @id_equation_1 : id. *)
Hint Rewrite @id_equation_1 : ID.

Corollary IDProp_equation_1 : IDProp = forall A : Prop, A -> A.
Proof. reflexivity. Qed.

Hint Rewrite @IDProp_equation_1 : IDProp.

Corollary idProp_equation_1 (A : Prop) (x : A) : idProp x = x.
Proof. reflexivity. Qed.

Hint Rewrite @idProp_equation_1 : idProp.

Corollary proj1_sig_equation_1 (A : Type) (P : A -> Prop) (a : A) (b : P a) :
  proj1_sig (exist P a b) = a.
Proof. reflexivity. Qed.

Hint Rewrite @proj1_sig_equation_1 : proj1_sig.

Corollary proj2_sig_equation_1 (A : Type) (P : A -> Prop) (a : A) (b : P a) :
  proj2_sig (exist P a b) = b.
Proof. reflexivity. Qed.

Hint Rewrite @proj2_sig_equation_1 : proj2_sig.

Corollary projT1_equation_1 (A : Type) (P : A -> Type) (a : A) (b : P a) :
  projT1 (existT P a b) = a.
Proof. reflexivity. Qed.

Hint Rewrite @projT1_equation_1 : projT1.

Corollary projT2_equation_1 (A : Type) (P : A -> Type) (a : A) (b : P a) :
  projT2 (existT P a b) = b.
Proof. reflexivity. Qed.

Hint Rewrite @projT2_equation_1 : projT2.

Corollary sig_of_sigT_equation_1 (A : Type) (P : A -> Prop) (a : A) (b : P a) :
  sig_of_sigT (existT P a b) = exist P a b.
Proof. reflexivity. Qed.

Hint Rewrite @sig_of_sigT_equation_1 : sig_of_sigT.

Corollary sigT_of_sig_equation_1 (A : Type) (P : A -> Prop) (a : A) (b : P a) :
  sigT_of_sig (exist P a b) = existT P a b.
Proof. reflexivity. Qed.

Hint Rewrite @sigT_of_sig_equation_1 : sig_of_sig.
