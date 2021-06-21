(** * Initialization for All Libraries *)

(** ** Imports and Exports *)

(** We export [StrictProp] to be able
    to use strict propositions without ceremony,
    export [Basics], [Tactics] and [Relations]
    to make their utility functions available everywhere,
    export [Morphisms], [DecidableClass] and [RelationClasses]
    to build a symbiotic relationship with the standard library,
    import [PArith], [NArith], [ZArith], [QArith],
    [Reals], [Int31] and [Int63] in order
    to redefine some of the basic numeral notations,
    import [List] to manually define some corollaries
    that would otherwise be automatically generated,
    export [Equations] to load the equations plugin.
    All of the imports and exports are carried out before setting options,
    because we want to ensure that the options we set are not overridden
    by other libraries. *)

From Coq Require Export
  Logic.StrictProp.
From Coq Require Export
  Program.Basics Program.Tactics Relations.Relations.
From Coq Require Export
  Classes.Morphisms Classes.DecidableClass Classes.RelationClasses.
From Coq Require Import
  PArith.PArith NArith.NArith ZArith.ZArith QArith.QArith Reals.Reals
  Numbers.Cyclic.Int31.Int31 Numbers.Cyclic.Int63.Int63.
From Coq Require Import
  Lists.List.
From Equations.Prop Require Export
  Equations.

(** ** Flags and Options and Tables *)

(** We disable warnings about unsupported attributes,
    because we use some custom attributes as refactoring hints. *)

#[global] Set Warnings "-unsupported-attributes".

(** We disable warnings about overriding notations,
    because we overload many standard library notations
    with operational typeclasses. *)

#[global] Set Warnings "-notation-overridden".

(** We turn on automatically inferred implicit arguments and
    make them maximally inserted and conservatively detected,
    since most typeclasses follow the same design pattern. *)

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

#[global] Obligation Tactic := try program_solve_wf.

(** We do not use implicit generalization,
    because the consequences of accidental misuse
    are worse than the convenience it permits. *)

#[global] Generalizable No Variables.

(** We reset the interpretation scope stack,
    because it is very sensitive to changes.
    The initial scope stack can be inspected
    with [Print Scopes] and [Print Visibility]. *)

#[global] Close Scope equations_scope.
#[global] Close Scope list_scope.
#[global] Close Scope Q_scope.
#[global] Close Scope bool_scope.
#[global] Close Scope nat_scope.
#[global] Close Scope type_scope.
#[global] Close Scope function_scope.
#[global] Close Scope core_scope.

#[global] Open Scope equations_scope.
#[global] Open Scope signature_scope.
#[global] Open Scope list_scope.
#[global] Open Scope bool_scope.
#[global] Open Scope nat_scope.
#[global] Open Scope type_scope.
#[global] Open Scope function_scope.
#[global] Open Scope core_scope.

(** We use anonymous goals and obligations to define local lemmas,
    which is why we do not want to see them in search results. *)

Add Search Blacklist "Unnamed_".
Add Search Blacklist "_obligation".

(** We do not want to see the obvious instances generated
    by the equations plugin either. *)

Add Search Blacklist "FunctionalElimination_".
Add Search Blacklist "FunctionalInduction_".

(** ** Reserved Notations *)

(** We reserve the following notations.
    While doing so is not strictly necessary,
    this list also serves as a quick reference. *)

Reserved Notation "'0'".
Reserved Notation "'1'".

Reserved Notation "A '->' B"
  (right associativity, at level 99, B at level 200).
Reserved Notation "A '<-' B"
  (left associativity, at level 98, B at level 199).
Reserved Notation "A '<->' B" (no associativity, at level 95).

Reserved Notation "x '=' y" (no associativity, at level 70).
Reserved Notation "x '<>' y" (no associativity, at level 70).

Reserved Notation "f '^-1'" (left associativity, at level 25).
Reserved Notation "g 'o' f" (left associativity, at level 40).

Reserved Notation "'~' x" (right associativity, at level 75).
Reserved Notation "x '/\' y" (right associativity, at level 80).
Reserved Notation "x '\/' y" (right associativity, at level 85).
Reserved Notation "y '<=' x" (no associativity, at level 70).
Reserved Notation "y '<' x" (no associativity, at level 70).
Reserved Notation "y '>=' x" (no associativity, at level 70).
Reserved Notation "y '>' x" (no associativity, at level 70).
Reserved Notation "x '+' y" (left associativity, at level 50).
Reserved Notation "'-' x" (right associativity, at level 35).
Reserved Notation "y '-' x" (left associativity, at level 50).
Reserved Notation "x '*' y" (left associativity, at level 40).
Reserved Notation "'/' x" (right associativity, at level 35).
Reserved Notation "y '/' x" (left associativity, at level 40).
Reserved Notation "y '^' x" (right associativity, at level 30).

Reserved Notation "'{' a '$' B '}'" (at level 0, a at level 99).
Reserved Notation "'{' a ':' A '$' B '}'" (at level 0, a at level 99).

Reserved Notation "R '==>' S" (right associativity, at level 55).
Reserved Notation "R '-->' S" (right associativity, at level 55).
Reserved Notation "R '<==' S" (right associativity, at level 55).
Reserved Notation "R '<--' S" (right associativity, at level 55).
Reserved Notation "R '<==>' S" (right associativity, at level 55).
Reserved Notation "R '<-->' S" (right associativity, at level 55).

Reserved Notation "x '==' y" (no associativity, at level 70).
Reserved Notation "x '===' y" (no associativity, at level 70).

(** ** Numeral Definitions *)

(** We export the [rew] notations from [Init.Logic]
    to use them like transport in homotopy type theory. *)

Export EqNotations.
Import ListNotations.

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

(** We extend the following standard library modules. *)

Module Decimal.

Export Coq.Init.Decimal.

Notation "'0'" := (D0 Nil) : dec_uint_scope.
Notation "'1'" := (D1 Nil) : dec_uint_scope.

Notation "'0'" := (Pos (D0 Nil)) : dec_int_scope.
Notation "'1'" := (Pos (D1 Nil)) : dec_int_scope.

End Decimal.

Module Hexadecimal.

Export Coq.Init.Hexadecimal.

Notation "'0'" := (D0 Nil) : hex_uint_scope.
Notation "'1'" := (D1 Nil) : hex_uint_scope.

Notation "'0'" := (Pos (D0 Nil)) : hex_int_scope.
Notation "'1'" := (Pos (D1 Nil)) : hex_int_scope.

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

(** ** Types and Propositional Connectives *)

(** Partially applied notations (operator sections)
    can be generated from the fully applied versions,
    although they have to be declared first,
    so that partial applications are not printed
    when full applications are present. *)

Notation "'_->_'" := (fun A B : _ => forall _ : A, B) : type_scope.
Notation "A '->' B" := (forall _ : A, B) : type_scope.
Notation "'_<->_'" := iff : type_scope.
Notation "A '<->' B" := (iff A B) : type_scope.

(** We embrace the groupoid structure of the identity type. *)

Notation "'_=_'" := eq : type_scope.
Notation "x '=' y" := (eq x y) : type_scope.
Notation "'_<>_'" := (fun x y : _ => not (eq x y)) : type_scope.
Notation "x '<>' y" := (not (eq x y)) : type_scope.

Notation "'id'" := eq_refl : type_scope.
Notation "'_^-1'" := eq_sym : type_scope.
Notation "a '^-1'" := (eq_sym a) : type_scope.
Notation "'_o_'" := eq_trans : type_scope.
Notation "b 'o' a" := (eq_trans a b) : type_scope.

Notation "'~_'" := not : type_scope.
Notation "'~' A" := (not A) : type_scope.
Notation "'-_'" := notT : type_scope.
Notation "'-' A" := (notT A) : type_scope.
Notation "'_/\_'" := and : type_scope.
Notation "A '/\' B" := (and A B) : type_scope.
Notation "'_\/_'" := or : type_scope.
Notation "A '\/' B" := (or A B) : type_scope.

(** We adapt the convention that each lemma declared as a [Corollary]
    could be generated by the equations plugin. *)

Corollary iff_equation_1 (A B : Prop) :
  (A <-> B) = ((A -> B) /\ (B -> A)).
Proof. reflexivity. Qed.

#[export] Hint Rewrite @iff_equation_1 : iff.

Corollary all_equation_1 (A : Prop) (P : A -> Prop) :
  all P = forall x : A, P x.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @all_equation_1 : all.

(** There are two different [subrelation] definitions
    in the standard library for some reason. *)

Corollary subrelation_equation_1 (A B : Type) (R R' : A -> B -> Prop) :
  Init.Logic.subrelation R R' = forall (x : A) (y : B), R x y -> R' x y.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @subrelation_equation_1 : subrelation.

Corollary unique_equation_1 (A : Type) (P : A -> Prop) (x : A) :
  unique P x = (P x /\ forall x' : A, P x' -> x = x').
Proof. reflexivity. Qed.

#[export] Hint Rewrite @unique_equation_1 : unique.

Corollary uniqueness_equation_1 (A : Type) (P : A -> Prop) :
  uniqueness P = forall x y : A, P x -> P y -> x = y.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @uniqueness_equation_1 : uniqueness.

(** ** Datatypes *)

Section Context.

#[local] Open Scope bool_scope.

Corollary andb_equation_1 (b1 b2 : bool) :
  true && b2 = b2.
Proof. reflexivity. Qed.

Corollary andb_equation_2 (b1 b2 : bool) :
  false && b2 = false.
Proof. reflexivity. Qed.

Corollary orb_equation_1 (b1 b2 : bool) :
  true || b2 = true.
Proof. reflexivity. Qed.

Corollary orb_equation_2 (b1 b2 : bool) :
  false || b2 = b2.
Proof. reflexivity. Qed.

Corollary implb_equation_1 (b1 b2 : bool) :
  implb true b2 = b2.
Proof. reflexivity. Qed.

Corollary implb_equation_2 (b1 b2 : bool) :
  implb false b2 = true.
Proof. reflexivity. Qed.

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

Corollary negb_equation_1 (b : bool) :
  negb true = false.
Proof. reflexivity. Qed.

Corollary negb_equation_2 (b : bool) :
  negb false = true.
Proof. reflexivity. Qed.

Corollary is_true_equation_1 (b : bool) :
  is_true b = (b = true).
Proof. reflexivity. Qed.

End Context.

#[export] Hint Rewrite @andb_equation_1 @andb_equation_2 : andb.
#[export] Hint Rewrite @orb_equation_1 @orb_equation_2 : orb.
#[export] Hint Rewrite @implb_equation_1 @implb_equation_2 : implb.
#[export] Hint Rewrite @xorb_equation_1 @xorb_equation_2
  @xorb_equation_3 @xorb_equation_4 : xorb.
#[export] Hint Rewrite @negb_equation_1 @negb_equation_2 : negb.
#[export] Hint Rewrite @is_true_equation_1 : is_true.

(** We might as well treat booleans as reflections of propositions. *)

Coercion is_true : bool >-> Sortclass.

Corollary option_map_equation_1 (A B : Type) (f : A -> B) (a : A) :
  option_map f (Some a) = Some (f a).
Proof. reflexivity. Qed.

Corollary option_map_equation_2 (A B : Type) (f : A -> B) :
  option_map f None = None.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @option_map_equation_1
  @option_map_equation_2 : option_map.

Notation "'_+_'" := sum : type_scope.
Notation "A '+' B" := (sum A B) : type_scope.
Notation "'_*_'" := prod : type_scope.
Notation "A '*' B" := (prod A B) : type_scope.

Corollary fst_equation_1 (A B : Type) (x : A) (y : B) : fst (x, y) = x.
Proof. reflexivity. Qed.

Corollary snd_equation_1 (A B : Type) (x : A) (y : B) : snd (x, y) = y.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @fst_equation_1 : fst.
#[export] Hint Rewrite @snd_equation_1 : snd.

Corollary length_equation_1 (A : Type) :
  length (A := A) [] = O.
Proof. reflexivity. Qed.

Corollary length_equation_2 (A : Type) (a : A) (l' : list A) :
  length (a :: l') = S (length l').
Proof. reflexivity. Qed.

#[export] Hint Rewrite @length_equation_1 @length_equation_2 : length.

Corollary app_equation_1 (A : Type) (m : list A) :
  [] ++ m = m.
Proof. reflexivity. Qed.

Corollary app_equation_2 (A : Type) (a : A) (l1 m : list A) :
  (a :: l1) ++ m = a :: (l1 ++ m).
Proof. reflexivity. Qed.

#[export] Hint Rewrite @app_equation_1 @app_equation_2 : app.

Corollary ID_equation_1 : ID = forall A : Type, A -> A.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @ID_equation_1 : ID.

(** We define a new identity function and
    turn [id] into a keyword to reuse it with concepts like categories.
    If we created a hint database called [id],
    we could never refer to it again,
    because hint databases cannot handle qualified names. *)

Equations idfun (A : Type) (x : A) : A :=
  idfun x := x.

Notation "'id'" := idfun : core_scope.

Corollary IDProp_equation_1 : IDProp = forall A : Prop, A -> A.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @IDProp_equation_1 : IDProp.

Corollary idProp_equation_1 (A : Prop) (x : A) : idProp x = x.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @idProp_equation_1 : idProp.

(** ** Subsets and Existential Types *)

Corollary ex_proj1_equation_1 (A : Prop) (P : A -> Prop) (a : A) (b : P a) :
  ex_proj1 (ex_intro P a b) = a.
Proof. reflexivity. Qed.

Corollary ex_proj2_equation_1 (A : Prop) (P : A -> Prop) (a : A) (b : P a) :
  ex_proj2 (ex_intro P a b) = b.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @ex_proj1_equation_1 : ex_proj1.
#[export] Hint Rewrite @ex_proj2_equation_1 : ex_proj2.

Corollary proj1_sig_equation_1 (A : Type) (P : A -> Prop) (a : A) (b : P a) :
  proj1_sig (exist P a b) = a.
Proof. reflexivity. Qed.

Corollary proj2_sig_equation_1 (A : Type) (P : A -> Prop) (a : A) (b : P a) :
  proj2_sig (exist P a b) = b.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @proj1_sig_equation_1 : proj1_sig.
#[export] Hint Rewrite @proj2_sig_equation_1 : proj2_sig.

Corollary projT1_equation_1 (A : Type) (P : A -> Type) (a : A) (b : P a) :
  projT1 (existT P a b) = a.
Proof. reflexivity. Qed.

Corollary projT2_equation_1 (A : Type) (P : A -> Type) (a : A) (b : P a) :
  projT2 (existT P a b) = b.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @projT1_equation_1 : projT1.
#[export] Hint Rewrite @projT2_equation_1 : projT2.

(** We should have similar notations for [Ssig] as there are for [sig].
    The mnemonic for [$] in the notation is that it is a combination
    of [|] from the notation for [sig] and [S] from the name of [Ssig].
    Besides, using [!] would conflict with
    the lonely notations of the equations plugin. *)

Notation "'{_$_}'" := Ssig : type_scope.
Notation "'{' a '$' B '}'" := (Ssig (fun a : _ => B)) : type_scope.
Notation "'{_:_$_}'" := @Ssig : type_scope.
Notation "'{' a ':' A '$' B '}'" := (@Ssig A (fun a : _ => B)) : type_scope.

Section Context.

#[local] Set Cumulative StrictProp.

Corollary Spr1_equation_1 (A : Type) (P : A -> SProp) (a : A) (b : P a) :
  Spr1 (Sexists P a b) = a.
Proof. reflexivity. Qed.

Corollary Spr2_equation_1 (A : Type) (P : A -> SProp) (a : A) (b : P a) :
  Spr2 (Sexists P a b) = b.
Proof. reflexivity. Qed.

End Context.

#[export] Hint Rewrite @Spr1_equation_1 : Spr1.
#[export] Hint Rewrite @Spr2_equation_1 : Spr2.

Corollary sig_of_sigT_equation_1 (A : Type) (P : A -> Prop) (a : A) (b : P a) :
  sig_of_sigT (existT P a b) = exist P a b.
Proof. reflexivity. Qed.

Corollary sigT_of_sig_equation_1 (A : Type) (P : A -> Prop) (a : A) (b : P a) :
  sigT_of_sig (exist P a b) = existT P a b.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @sig_of_sigT_equation_1 : sig_of_sigT.
#[export] Hint Rewrite @sigT_of_sig_equation_1 : sig_of_sig.

(** ** Basic Functions and Combinators *)

(** While some standard library definitions
    need to be overridden with more sensible versions,
    most of them are totally fine,
    in which case we just accompany them with dependent versions. *)

Fail Fail Equations compose (A B C : Type)
  (g : B -> C) (f : A -> B) (a : A) : C :=
  compose g f a := g (f a).

(** Using [o] as a variable name should be prohibited by law,
    which is why we turn it into a notation instead. *)

Notation "'_o_'" := compose : core_scope.
Notation "g 'o' f" := (compose g f) : core_scope.

Corollary compose_equation_1 (A B C : Type)
  (g : B -> C) (f : A -> B) (x : A) :
  (g o f) x = g (f x).
Proof. reflexivity. Qed.

#[export] Hint Rewrite @compose_equation_1 : compose.

Equations compose_dep
  (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type)
  (g : forall (a : A) (b : P a), Q a b) (f : forall a : A, P a)
  (a : A) : Q a (f a) :=
  compose_dep g f a := g a (f a).

Fail Fail Equations arrow (A B : Type) : Type :=
  arrow A B := A -> B.

Corollary arrow_equation_1 (A B : Type) : arrow A B = (A -> B).
Proof. reflexivity. Qed.

#[export] Hint Rewrite @arrow_equation_1 : arrow.

Fail Fail Equations impl (A B : Prop) : Prop :=
  impl A B := A -> B.

Corollary impl_equation_1 (A B : Prop) : impl A B = (A -> B).
Proof. reflexivity. Qed.

#[export] Hint Rewrite @impl_equation_1 : impl.

Fail Fail Equations const (A B : Type) (a : A) (b : B) : A :=
  const a b := a.

Corollary const_equation_1 (A B : Type) (a : A) (b : B) : const a b = a.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @const_equation_1 : const.

Equations const_dep (A : Type) (P : A -> Type) (a : A) (b : P a) : A :=
  const_dep _ a b := a.

Fail Fail Equations flip (A B C : Type)
  (f : A -> B -> C) (b : B) (a : A) : C :=
  flip f b a := f a b.

Corollary flip_equation_1 (A B C : Type) (f : A -> B -> C) (x : B) (y : A) :
  flip f x y = f y x.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @flip_equation_1 : flip.

Equations flip_dep (A B : Type) (P : A -> B -> Type)
  (f : forall (a : A) (b : B), P a b) (b : B) (a : A) : P a b :=
  flip_dep f b a := f a b.

Fail Fail Equations apply (A B : Type) (f : A -> B) (a : A) : B :=
  apply f a := f a.

Corollary apply_equation_1 (A B : Type) (f : A -> B) (x : A) :
  apply f x = f x.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @apply_equation_1 : apply.

Equations apply_dep (A : Type) (P : A -> Type)
  (f : forall a : A, P a) (a : A) : P a :=
  apply_dep f a := f a.

(** ** Respectful Morphisms *)

(** Respectful morphisms have an obvious dual
    that is missing from the standard library. *)

Fail Fail Equations respectful (A B : Type)
  (R : relation A) (R' : relation B) : relation (A -> B) :=
  respectful R R' := fun f g : A -> B =>
  forall x y : A, R x y -> R' (f x) (g y).

Corollary respectful_equation_1
  (A B : Type) (R : relation A) (R' : relation B) :
  respectful R R' = fun f g : A -> B =>
  forall x y : A, R x y -> R' (f x) (g y).
Proof. reflexivity. Qed.

#[export] Hint Rewrite @respectful_equation_1 : respectful.

Notation "'_==>_'" := respectful : signature_scope.
Notation "R '==>' S" := (respectful R S) : signature_scope.

Fail Fail Equations respectful_hetero
  (A B : Type) (C : A -> Type) (D : B -> Type)
  (R : A -> B -> Prop) (R' : forall (x : A) (y : B), C x -> D y -> Prop)
  (f : forall x : A, C x) (g : forall x : B, D x) : Prop :=
  respectful_hetero R R' :=
  fun (f : forall x : A, C x) (g : forall x : B, D x) =>
  forall (x : A) (y : B), R x y -> R' x y (f x) (g y).

Corollary respectful_hetero_equation_1
  (A B : Type) (C : A -> Type) (D : B -> Type)
  (R : A -> B -> Prop) (R' : forall (x : A) (y : B), C x -> D y -> Prop) :
  respectful_hetero A B C D R R' =
  fun (f : forall x : A, C x) (g : forall x : B, D x) =>
  forall (x : A) (y : B), R x y -> R' x y (f x) (g y).
Proof. reflexivity. Qed.

#[export] Hint Rewrite @respectful_hetero_equation_1 : respectful_hetero.

Equations corespectful (A B : Type)
  (R : relation B) (R' : relation A) : relation (A -> B) :=
  corespectful R R' := fun f g : A -> B =>
  forall x y : A, R (f x) (g y) -> R' x y.

Notation "'_<==_'" := corespectful : signature_scope.
Notation "R '<==' S" := (corespectful R S) : signature_scope.

Equations corespectful_hetero
  (A B : Type) (C : A -> Type) (D : B -> Type)
  (R : forall (x : A) (y : B), C x -> D y -> Prop) (R' : A -> B -> Prop) :
  (forall x : A, C x) -> (forall x : B, D x) -> Prop :=
  corespectful_hetero R R' :=
  fun (f : forall x : A, C x) (g : forall x : B, D x) =>
  forall (x : A) (y : B), R x y (f x) (g y) -> R' x y.

Equations birespectful (A B C : Type)
  (R : relation B) (R' : relation C) : relation ((A -> B) * (A -> C)) :=
  birespectful R R' := fun fh gk : (A -> B) * (A -> C) =>
  forall x y : A, R (fst fh x) (fst gk y) -> R' (snd fh x) (snd gk y).

Notation "'_<==>_'" := birespectful : signature_scope.
Notation "R '<==>' S" := (birespectful R S) : signature_scope.

Equations birespectful_hetero (A B : Type)
  (C : A -> Type) (D : B -> Type) (E : A -> Type) (F : B -> Type)
  (R : forall (x : A) (y : B), C x -> D y -> Prop)
  (R' : forall (x : A) (y : B), E x -> F y -> Prop) :
  (forall x : A, C x) * (forall x : A, E x) ->
  (forall x : B, D x) * (forall x : B, F x) -> Prop :=
  birespectful_hetero R R' :=
  fun (fh : (forall x : A, C x) * (forall x : A, E x))
  (gk : (forall x : B, D x) * (forall x : B, F x)) =>
  forall (x : A) (y : B),
  R x y (fst fh x) (fst gk y) -> R' x y (snd fh x) (snd gk y).

(** ** Currying and Uncurrying *)

(** Currying and uncurrying are swapped around
    in some versions of the standard library and
    not defined for all product types,
    which is why we redefine them all here. *)

Equations conj_curry (A B C : Prop)
  (f : A /\ B -> C) (a : A) (b : B) : C :=
  conj_curry f a b := f (conj a b).

Equations conj_uncurry (A B C : Prop)
  (f : A -> B -> C) (x : A /\ B) : C :=
  conj_uncurry f (conj a b) := f a b.

Equations ex_curry (A : Prop) (P : A -> Prop) (B : Prop)
  (f : (exists a : A, P a) -> B) (a : A) (b : P a) : B :=
  ex_curry f a b := f (ex_intro P a b).

Equations ex_uncurry (A : Prop) (P : A -> Prop) (B : Prop)
  (f : forall a : A, P a -> B) (x : exists a : A, P a) : B :=
  ex_uncurry f (ex_intro _ a b) := f a b.

(** The equations plugin does not generate projection lemmas,
    which is why we have to write them by hand. *)

Lemma ex_uncurry_proj (A : Prop) (P : A -> Prop) (B : Prop)
  (f : forall a : A, P a -> B) (x : exists a : A, P a) :
  ex_uncurry f x = f (ex_proj1 x) (ex_proj2 x).
Proof. destruct x as [a b]. reflexivity. Qed.

Equations ex_curry_dep
  (A : Prop) (P : A -> Prop) (Q : forall a : A, P a -> Prop)
  (f : forall x : exists a : A, P a, Q (ex_proj1 x) (ex_proj2 x))
  (a : A) (b : P a) : Q a b :=
  ex_curry_dep _ f a b := f (ex_intro P a b).

Equations ex_uncurry_dep
  (A : Prop) (P : A -> Prop) (Q : forall a : A, P a -> Prop)
  (f : forall (a : A) (b : P a), Q a b)
  (x : exists a : A, P a) : Q (ex_proj1 x) (ex_proj2 x) :=
  ex_uncurry_dep f (ex_intro _ a b) := f a b.

Lemma ex_uncurry_dep_proj
  (A : Prop) (P : A -> Prop) (Q : forall a : A, P a -> Prop)
  (f : forall (a : A) (b : P a), Q a b)
  (x : exists a : A, P a) :
  ex_uncurry_dep f x = f (ex_proj1 x) (ex_proj2 x).
Proof. destruct x as [a b]. reflexivity. Qed.

Equations prod_curry (A B C : Type)
  (f : A * B -> C) (a : A) (b : B) : C :=
  prod_curry f a b := f (a, b).

Equations prod_uncurry (A B C : Type)
  (f : A -> B -> C) (x : A * B) : C :=
  prod_uncurry f (a, b) := f a b.

Lemma prod_uncurry_proj (A B C : Type)
  (f : A -> B -> C) (x : A * B) :
  prod_uncurry f x = f (fst x) (snd x).
Proof. destruct x as [a b]. reflexivity. Qed.

Equations prod_curry_dep (A B : Type) (P : A -> B -> Type)
  (f : forall x : A * B, P (fst x) (snd x)) (a : A) (b : B) : P a b :=
  prod_curry_dep _ f a b := f (a, b).

Equations prod_uncurry_dep (A B : Type) (P : A -> B -> Type)
  (f : forall (a : A) (b : B), P a b) (x : A * B) : P (fst x) (snd x) :=
  prod_uncurry_dep f (a, b) := f a b.

Lemma prod_uncurry_dep_proj (A B : Type) (P : A -> B -> Type)
  (f : forall (a : A) (b : B), P a b) (x : A * B) :
  prod_uncurry_dep f x = f (fst x) (snd x).
Proof. destruct x as [a b]. reflexivity. Qed.

Equations sig_curry (A : Type) (P : A -> Prop) (B : Type)
  (f : {a : A | P a} -> B) (a : A) (b : P a) : B :=
  sig_curry f a b := f (exist P a b).

Equations sig_uncurry (A : Type) (P : A -> Prop) (B : Type)
  (f : forall a : A, P a -> B) (x : {a : A | P a}) : B :=
  sig_uncurry f (exist _ a b) := f a b.

Lemma sig_uncurry_proj (A : Type) (P : A -> Prop) (B : Type)
  (f : forall a : A, P a -> B) (x : {a : A | P a}) :
  sig_uncurry f x = f (proj1_sig x) (proj2_sig x).
Proof. destruct x as [a b]. reflexivity. Qed.

Equations sig_curry_dep
  (A : Type) (P : A -> Prop) (Q : forall a : A, P a -> Type)
  (f : forall x : {a : A | P a}, Q (proj1_sig x) (proj2_sig x))
  (a : A) (b : P a) : Q a b :=
  sig_curry_dep _ f a b := f (exist P a b).

Equations sig_uncurry_dep
  (A : Type) (P : A -> Prop) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (x : {a : A | P a}) : Q (proj1_sig x) (proj2_sig x) :=
  sig_uncurry_dep f (exist _ a b) := f a b.

Lemma sig_uncurry_dep_proj
  (A : Type) (P : A -> Prop) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (x : {a : A | P a}) :
  sig_uncurry_dep f x = f (proj1_sig x) (proj2_sig x).
Proof. destruct x as [a b]. reflexivity. Qed.

Equations sigT_curry (A : Type) (P : A -> Type) (B : Type)
  (f : {a : A & P a} -> B) (a : A) (b : P a) : B :=
  sigT_curry f a b := f (existT P a b).

Equations sigT_uncurry (A : Type) (P : A -> Type) (B : Type)
  (f : forall a : A, P a -> B) (x : {a : A & P a}) : B :=
  sigT_uncurry f (existT _ a b) := f a b.

Lemma sigT_uncurry_proj (A : Type) (P : A -> Type) (B : Type)
  (f : forall a : A, P a -> B) (x : {a : A & P a}) :
  sigT_uncurry f x = f (projT1 x) (projT2 x).
Proof. destruct x as [a b]. reflexivity. Qed.

Equations sigT_curry_dep
  (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type)
  (f : forall x : {a : A & P a}, Q (projT1 x) (projT2 x))
  (a : A) (b : P a) : Q a b :=
  sigT_curry_dep _ f a b := f (existT P a b).

Equations sigT_uncurry_dep
  (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (x : {a : A & P a}) : Q (projT1 x) (projT2 x) :=
  sigT_uncurry_dep f (existT _ a b) := f a b.

Lemma sigT_uncurry_dep_proj
  (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (x : {a : A & P a}) :
  sigT_uncurry_dep f x = f (projT1 x) (projT2 x).
Proof. destruct x as [a b]. reflexivity. Qed.

Equations Ssig_curry (A : Type) (P : A -> SProp) (B : Type)
  (f : {a : A $ P a} -> B) (a : A) (b : P a) : B :=
  Ssig_curry f a b := f (Sexists P a b).

Equations Ssig_uncurry (A : Type) (P : A -> SProp) (B : Type)
  (f : forall a : A, P a -> B) (x : {a : A $ P a}) : B :=
  Ssig_uncurry f (Sexists _ a b) := f a b.

Lemma Ssig_uncurry_proj (A : Type) (P : A -> SProp) (B : Type)
  (f : forall a : A, P a -> B) (x : {a : A $ P a}) :
  Ssig_uncurry f x = f (Spr1 x) (Spr2 x).
Proof. destruct x as [a b]. reflexivity. Qed.

Equations Ssig_curry_dep
  (A : Type) (P : A -> SProp) (Q : forall a : A, P a -> Type)
  (f : forall x : {a : A $ P a}, Q (Spr1 x) (Spr2 x))
  (a : A) (b : P a) : Q a b :=
  Ssig_curry_dep _ f a b := f (Sexists P a b).

Equations Ssig_uncurry_dep
  (A : Type) (P : A -> SProp) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (x : {a : A $ P a}) : Q (Spr1 x) (Spr2 x) :=
  Ssig_uncurry_dep f (Sexists _ a b) := f a b.

Lemma Ssig_uncurry_dep_proj
  (A : Type) (P : A -> SProp) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (x : {a : A $ P a}) :
  Ssig_uncurry_dep f x = f (Spr1 x) (Spr2 x).
Proof. destruct x as [a b]. reflexivity. Qed.

(** ** Implicit Arguments *)

(** We adjust the implicit arguments of [ex], [sig], [sigT], [Ssig] and
    several other standard library functions to behave the same way. *)

Arguments eq_refl {_ _}.
Arguments eq_sym {_ _ _} _.
Arguments eq_trans {_ _ _ _} _ _.

Arguments iff _ _ /.
Arguments all {_} _ /.
Arguments Init.Logic.subrelation {_ _} _ _ /.
Arguments unique {_} _ _ /.
Arguments uniqueness {_} _ /.

Arguments andb !_ _.
Arguments orb !_ _.
Arguments implb !_ _.
Arguments xorb !_ !_.
Arguments negb !_.
Arguments is_true !_.
Arguments option_map {_ _} _ !_.
Arguments fst {_ _} !_.
Arguments snd {_ _} !_.
Arguments length {_} !_.
Arguments app {_} !_ _.
Arguments ID /.
Arguments idfun {_} _ /.
Arguments IDProp /.
Arguments idProp {_} _ /.

Arguments ex {_} _.
Arguments ex_intro {_} _ _ _.
Arguments ex_proj1 {_ _} !_.
Arguments ex_proj2 {_ _} !_.
Arguments sig {_} _.
Arguments exist {_} _ _ _.
Arguments proj1_sig {_ _} !_.
Arguments proj2_sig {_ _} !_.
Arguments sigT {_} _.
Arguments existT {_} _ _ _.
Arguments projT1 {_ _} !_.
Arguments projT2 {_ _} !_.
Arguments Ssig {_} _.
Arguments Sexists {_} _ _ _.
Arguments Spr1 {_ _} !_.
Arguments Spr2 {_ _} !_.
Arguments sig_of_sigT {_ _} !_.
Arguments sigT_of_sig {_ _} !_.

Arguments compose {_ _ _} _ _ _ /.
Arguments compose_dep {_ _ _} _ _ _ /.
Arguments arrow _ _ /.
Arguments impl _ _ /.
Arguments const {_ _} _ _ /.
Arguments const_dep {_ _} _ _ /.
Arguments flip {_ _ _} _ _ _ /.
Arguments flip_dep {_ _ _} _ _ _ /.
Arguments apply {_ _} _ _ /.
Arguments apply_dep {_ _} _ _ /.

Arguments respectful {_ _} !_.
Arguments corespectful {_ _} !_.
Arguments birespectful {_ _} !_.

Arguments conj_curry {_ _ _} _ _ _ /.
Arguments conj_uncurry {_ _ _} _ !_.
Arguments ex_curry {_ _ _} _ _ _ /.
Arguments ex_curry_dep {_ _ _} _ _ _ /.
Arguments ex_uncurry {_ _ _} _ !_.
Arguments ex_uncurry_dep {_ _ _} _ !_.
Arguments prod_curry {_ _ _} _ _ _ /.
Arguments prod_curry_dep {_ _ _} _ _ _ /.
Arguments prod_uncurry {_ _ _} _ !_.
Arguments prod_uncurry_dep {_ _ _} _ !_.
Arguments sig_curry {_ _ _} _ _ _ /.
Arguments sig_curry_dep {_ _ _} _ _ _ /.
Arguments sig_uncurry {_ _ _} _ !_.
Arguments sig_uncurry_dep {_ _ _} _ !_.
Arguments sigT_curry {_ _ _} _ _ _ /.
Arguments sigT_curry_dep {_ _ _} _ _ _ /.
Arguments sigT_uncurry {_ _ _} _ !_.
Arguments sigT_uncurry_dep {_ _ _} _ !_.
Arguments Ssig_curry {_ _ _} _ _ _ /.
Arguments Ssig_curry_dep {_ _ _} _ _ _ /.
Arguments Ssig_uncurry {_ _ _} _ !_.
Arguments Ssig_uncurry_dep {_ _ _} _ !_.

(** ** Opacity and Transparency *)

(** Flip these switches and push those carts to make unification smart. *)

Typeclasses Opaque iff all Init.Logic.subrelation unique uniqueness.

Typeclasses Transparent andb orb implb xorb negb is_true
  option_map fst snd length app ID idfun IDProp idProp.

Typeclasses Transparent ex_proj1 ex_proj2 proj1_sig proj2_sig
  projT1 projT2 Spr1 Spr2 sig_of_sigT sigT_of_sig.

Typeclasses Transparent compose compose_dep arrow impl
  const const_dep flip flip_dep apply apply_dep.

Typeclasses Opaque respectful corespectful birespectful.

Typeclasses Transparent conj_curry conj_uncurry
  ex_curry ex_curry_dep ex_uncurry ex_uncurry_dep
  prod_curry prod_curry_dep prod_uncurry prod_uncurry_dep
  sig_curry sig_curry_dep sig_uncurry sig_uncurry_dep
  sigT_curry sigT_curry_dep sigT_uncurry sigT_uncurry_dep
  Ssig_curry Ssig_curry_dep Ssig_uncurry Ssig_uncurry_dep.

(** ** Missing Lemmas *)

(** This is another way to state [Spr1_inj]
    without breaking unification when universe polymorphism is turned off. *)

Lemma eq_Ssig (A : Type) (P : A -> SProp)
  (a0 : A) (b0 : P a0) (a1 : A) (b1 : P a1)
  (e : a0 = a1) : Sexists P a0 b0 = Sexists P a1 b1.
Proof. apply Spr1_inj. auto. Qed.

(** Composition and identity form a category. *)

Lemma compose_assoc (A B C D : Type)
  (h : C -> D) (g : B -> C) (f : A -> B) (a : A) :
  (h o (g o f)) a = ((h o g) o f) a.
Proof. reflexivity. Qed.

Lemma compose_id_l (A B : Type) (f : A -> B) (a : A) :
  (id o f) a = f a.
Proof. reflexivity. Qed.

Lemma compose_id_r (A B : Type) (f : A -> B) (a : A) :
  (f o id) a = f a.
Proof. reflexivity. Qed.

(** Dependent composition is more complicated and
    involves the S and K combinators. *)

Section Context.

#[local] Notation "'_o_'" := compose_dep : core_scope.
#[local] Notation "g 'o' f" := (compose_dep g f) : core_scope.

Lemma compose_dep_assoc
  (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type)
  (R : forall (a : A) (b : P a), Q a b -> Type)
  (h : forall (a : A) (b : P a) (c : Q a b), R a b c)
  (g : forall (a : A) (b : P a), Q a b) (f : forall a : A, P a) (a : A) :
  ((fun x : A => h _ _) o (g o f)) a = ((fun x : A => h _ o g _) o f) a.
  (* (h o (g o f)) a = ((h o g) o f) a *)
Proof. reflexivity. Qed.

Lemma compose_dep_id_l (A : Type) (P : A -> Type)
  (f : forall a : A, P a) (a : A) :
  ((fun x : A => id) o f) a = f a.
  (* (const id o f) a = f a *)
Proof. reflexivity. Qed.

Lemma compose_dep_id_r (A : Type) (P : A -> Type)
  (f : forall a : A, P a) (a : A) :
  ((fun x : A => f) o id) a = f a.
  (* (const f o id) a = f a *)
Proof. reflexivity. Qed.

End Context.

(** Flipping is a section and a retraction of itself,
    making it an involution. *)

Lemma flip_involutive (A B C : Type)
  (f : A -> B -> C) (a : A) (b : B) :
  flip (flip f) a b = f a b.
Proof. reflexivity. Qed.

Lemma flip_dep_involutive (A B : Type) (P : A -> B -> Type)
  (f : forall (a : A) (b : B), P a b) (b : B) (a : A) :
  flip_dep (flip_dep f) a b = f a b.
Proof. reflexivity. Qed.

(** Currying is both a section and a retraction of uncurrying. *)

Lemma eq_ex_uncurry_curry
  (A : Prop) (P : A -> Prop) (B : Prop)
  (f : (exists a : A, P a) -> B) (x : exists a : A, P a) :
  ex_uncurry (ex_curry f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_ex_curry_uncurry
  (A : Prop) (P : A -> Prop) (B : Prop)
  (f : forall a : A, P a -> B) (a : A) (b : P a) :
  ex_curry (ex_uncurry f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_ex_uncurry_dep_curry_dep
  (A : Prop) (P : A -> Prop) (Q : forall a : A, P a -> Prop)
  (f : forall x : exists a : A, P a, Q (ex_proj1 x) (ex_proj2 x))
  (x : exists a : A, P a) :
  ex_uncurry_dep (ex_curry_dep f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_ex_curry_dep_uncurry_dep
  (A : Prop) (P : A -> Prop) (Q : forall a : A, P a -> Prop)
  (f : forall (a : A) (b : P a), Q a b)
  (a : A) (b : P a) :
  ex_curry_dep (ex_uncurry_dep f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_prod_uncurry_curry (A B C : Type)
  (f : A * B -> C) (x : A * B) :
  prod_uncurry (prod_curry f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_prod_curry_uncurry (A B C : Type)
  (f : A -> B -> C) (a : A) (b : B) :
  prod_curry (prod_uncurry f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_prod_uncurry_dep_curry_dep (A B : Type) (P : A -> B -> Type)
  (f : forall x : A * B, P (fst x) (snd x)) (x : A * B) :
  prod_uncurry_dep (prod_curry_dep f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_prod_curry_dep_uncurry_dep (A B : Type) (P : A -> B -> Type)
  (f : forall (a : A) (b : B), P a b) (a : A) (b : B) :
  prod_curry_dep (prod_uncurry_dep f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_sig_uncurry_curry
  (A : Type) (P : A -> Prop) (B : Type)
  (f : {a : A | P a} -> B) (x : {a : A | P a}) :
  sig_uncurry (sig_curry f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_sig_curry_uncurry
  (A : Type) (P : A -> Prop) (B : Type)
  (f : forall a : A, P a -> B) (a : A) (b : P a) :
  sig_curry (sig_uncurry f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_sig_uncurry_dep_curry_dep
  (A : Type) (P : A -> Prop) (Q : forall a : A, P a -> Type)
  (f : forall x : {a : A | P a}, Q (proj1_sig x) (proj2_sig x))
  (x : {a : A | P a}) :
  sig_uncurry_dep (sig_curry_dep f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_sig_curry_dep_uncurry_dep
  (A : Type) (P : A -> Prop) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (a : A) (b : P a) :
  sig_curry_dep (sig_uncurry_dep f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_sigT_uncurry_curry
  (A : Type) (P : A -> Type) (B : Type)
  (f : {a : A & P a} -> B) (x : {a : A & P a}) :
  sigT_uncurry (sigT_curry f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_sigT_curry_uncurry
  (A : Type) (P : A -> Type) (B : Type)
  (f : forall a : A, P a -> B) (a : A) (b : P a) :
  sigT_curry (sigT_uncurry f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_sigT_uncurry_dep_curry_dep
  (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type)
  (f : forall x : {a : A & P a}, Q (projT1 x) (projT2 x))
  (x : {a : A & P a}) :
  sigT_uncurry_dep (sigT_curry_dep f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_sigT_curry_dep_uncurry_dep
  (A : Type) (P : A -> Type) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (a : A) (b : P a) :
  sigT_curry_dep (sigT_uncurry_dep f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_Ssig_uncurry_curry
  (A : Type) (P : A -> SProp) (B : Type)
  (f : {a : A $ P a} -> B) (x : {a : A $ P a}) :
  Ssig_uncurry (Ssig_curry f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_Ssig_curry_uncurry
  (A : Type) (P : A -> SProp) (B : Type)
  (f : forall a : A, P a -> B) (a : A) (b : P a) :
  Ssig_curry (Ssig_uncurry f) a b = f a b.
Proof. reflexivity. Qed.

Lemma eq_Ssig_uncurry_dep_curry_dep
  (A : Type) (P : A -> SProp) (Q : forall a : A, P a -> Type)
  (f : forall x : {a : A $ P a}, Q (Spr1 x) (Spr2 x))
  (x : {a : A $ P a}) :
  Ssig_uncurry_dep (Ssig_curry_dep f) x = f x.
Proof. destruct x as [a b]. reflexivity. Qed.

Lemma eq_Ssig_curry_dep_uncurry_dep
  (A : Type) (P : A -> SProp) (Q : forall a : A, P a -> Type)
  (f : forall (a : A) (b : P a), Q a b)
  (a : A) (b : P a) :
  Ssig_curry_dep (Ssig_uncurry_dep f) a b = f a b.
Proof. reflexivity. Qed.

(** The dependent and nondependent versions are related as follows. *)

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

Lemma eq_ex_curry_nondep (A : Prop) (P : A -> Prop) (B : Prop)
  (f : (exists a : A, P a) -> B) (a : A) (b : P a) :
  ex_curry_dep f a b = ex_curry f a b.
Proof. reflexivity. Qed.

Lemma eq_ex_uncurry_nondep (A : Prop) (P : A -> Prop) (B : Prop)
  (f : forall a : A, P a -> B) (x : exists a : A, P a) :
  ex_uncurry_dep f x = ex_uncurry f x.
Proof. destruct x as [a b]. reflexivity. Qed.

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
