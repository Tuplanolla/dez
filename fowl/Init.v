(** * Initialization for All Libraries *)

(** ** Imports and Exports *)

(** We import [String] to declare version information,
    export [StrictProp] to be able
    to use strict propositions without ceremony,
    export [Basics], [Tactics] and [Relations]
    to make their utility functions available everywhere,
    import [PArith], [NArith], [ZArith], [QArith],
    [Reals], [Int31] and [Int63] in order
    to redefine some of the basic numeral notations,
    import [List] to manually define some corollaries
    that would otherwise be automatically generated,
    export [Equations] to load the equations plugin.
    All of the imports and exports are carried out before setting options,
    because we want to ensure that the options we set are not overridden
    by other libraries. *)

From Coq Require Import
  Strings.String.
From Coq Require Export
  Logic.StrictProp.
From Coq Require Export
  Program.Basics Program.Tactics Relations.Relations.
From Coq Require Import
  PArith.PArith NArith.NArith ZArith.ZArith QArith.QArith QArith.Qcanon
  Reals.Reals Numbers.Cyclic.Int31.Int31 Numbers.Cyclic.Int63.Int63.
From Coq Require Import
  Lists.List.
From Equations.Prop Require Export
  Equations.

(** ** Version Information *)

(** We have tested this development with the following versions. *)

Definition Coq_Version := "8.15.0"%string.
Definition OCaml_Version := "4.12.0"%string.
Definition Equations_Version := "1.3"%string.

(** ** Flags, Options and Tables *)

(** We disable warnings about overriding notations,
    because we overload many standard library notations
    with operational typeclasses. *)

#[export] Set Warnings "-notation-overridden".

(** We turn on automatically inferred implicit arguments and
    make them maximally inserted and conservatively detected,
    since most typeclasses follow the same design pattern. *)

#[export] Set Implicit Arguments.
#[export] Set Maximal Implicit Insertion.
#[export] Set Strict Implicit.
#[export] Set Strongly Strict Implicit.
#[export] Unset Contextual Implicit.
#[export] Set Reversible Pattern Implicit.

(** We enable keyed unification,
    because [rewrite] does not work properly otherwise. *)

#[export] Set Keyed Unification.

(** We need to enable universe polymorphism
    for unification of strict propositions,
    even though the feature is experimental and
    incurs a considerable performance penalty on type checking. *)

#[export] Set Universe Polymorphism.
#[export] Unset Universe Minimization ToSet.

(** We mark equations transparent,
    because it may be necessary to [unfold] them manually
    when [simp] would either fail to progress or diverge. *)

#[export] Set Equations Transparent.

(** We do not allow automatic solution of obligations,
    because we do not want the addition or removal of hints
    to change the total number of obligations.

    The default tactic is
    [program_simplify;
    try typeclasses eauto 10 with program;
    try program_solve_wf]
    of which we keep the predictable parts of [program_simplify] and
    the entirety [program_solve_wf]. *)

#[global] Obligation Tactic := cbv beta; try program_solve_wf.

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

Reserved Notation "x '->' y"
  (right associativity, at level 99, y at level 200).
Reserved Notation "x '<-' y"
  (right associativity, at level 99, y at level 200).
Reserved Notation "x '<->' y"
  (no associativity, at level 95).

Reserved Notation "x '=' y" (no associativity, at level 70).
Reserved Notation "x '<>' y" (no associativity, at level 70).

Reserved Notation "'id'" (at level 0).
Reserved Notation "x '^-1'" (left associativity, at level 25).
Reserved Notation "y 'o' x" (left associativity, at level 40).

Reserved Notation "'~' x" (right associativity, at level 75).
Reserved Notation "x '\/' y" (right associativity, at level 85).
Reserved Notation "x '/\' y" (right associativity, at level 80).
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

Reserved Notation "'(' x ',' y ',' .. ',' z ')'" (at level 0).
Reserved Notation "'(' x ';' .. ';' y ';' z ')'" (at level 0).

Reserved Notation "'{' x '|' y '}'" (at level 0, x at level 99).
Reserved Notation "'{' x ':' A '|' y '}'" (at level 0, x at level 99).
Reserved Notation "'{' x '&' y '}'" (at level 0, x at level 99).
Reserved Notation "'{' x ':' A '&' y '}'" (at level 0, x at level 99).
Reserved Notation "'{' x '$' y '}'" (at level 0, x at level 99).
Reserved Notation "'{' x ':' A '$' y '}'" (at level 0, x at level 99).

Reserved Notation "'inspect' x" (no associativity, at level 0).
Reserved Notation "x 'eqn' ':' a" (no associativity, at level 100).

Reserved Notation "x '==>' y" (right associativity, at level 55).
Reserved Notation "x '-->' y" (right associativity, at level 55).
Reserved Notation "x '<==' y" (right associativity, at level 55).
Reserved Notation "x '<--' y" (right associativity, at level 55).
Reserved Notation "x '<==>' y" (no associativity, at level 45).
Reserved Notation "x '<-->' y" (no associativity, at level 45).

Reserved Notation "x '==' y" (no associativity, at level 70).
Reserved Notation "x '===' y" (no associativity, at level 70).

(** ** Number Definitions *)

(** We export the [rew] notations from [Logic]
    to use them like transport from homotopy type theory. *)

Export EqNotations.
Import ListNotations.

(** Number notations require their own little song and dance. *)

Module Reified.

Variant PropR : Type :=
  | FalseR
  | TrueR.

Definition PropR_of_Z (n : Z) : option PropR :=
  match n with
  | Z0 => Some FalseR
  | Zpos xH => Some TrueR
  | _ => None
  end.

Definition Z_of_PropR (A : PropR) : option Z :=
  match A with
  | FalseR => Some Z0
  | TrueR => Some (Zpos xH)
  end.

Module Notations.

#[local] Notation Prop' := Prop (only parsing).

Number Notation Prop' PropR_of_Z Z_of_PropR (via PropR mapping [
  True => TrueR,
  False => FalseR]) : type_scope.

End Notations.

End Reified.

Export Reified.Notations.

(** ** Types and Propositional Connectives *)

(** Partially applied notations (operator sections)
    can be generated from the fully applied versions,
    although they have to be declared first,
    so that partial applications are not printed
    when full applications are present. *)

Arguments eq_refl {_ _}.
Arguments eq_sym {_ _ _} _.
Arguments eq_trans {_ _ _ _} _ _.

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

Notation "'_->_'" := (fun A B : _ => forall _ : A, B) : type_scope.
Notation "A '->' B" := (forall _ : A, B) : type_scope.
Notation "'~_'" := not : type_scope.
Notation "'~' A" := (not A) : type_scope.
Notation "'-_'" := notT : type_scope.
Notation "'-' A" := (notT A) : type_scope.
Notation "'_\/_'" := or : type_scope.
Notation "A '\/' B" := (or A B) : type_scope.
Notation "'_/\_'" := and : type_scope.
Notation "A '/\' B" := (and A B) : type_scope.

(** We adapt the convention that each lemma declared as a [Corollary]
    could be generated by the equations plugin. *)

Corollary iff_equation_1 (A B : Prop) :
  iff A B = ((A -> B) /\ (B -> A)).
Proof. reflexivity. Qed.

#[export] Hint Rewrite @iff_equation_1 : iff.

Arguments iff _ _ /.

Notation "'_<->_'" := iff : type_scope.
Notation "A '<->' B" := (iff A B) : type_scope.

Corollary all_equation_1 (A : Prop) (P : A -> Prop) :
  all P = forall x : A, P x.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @all_equation_1 : all.

Arguments all {_} _ /.

(** There are two different [subrelation] definitions
    in the standard library for some reason. *)

Corollary subrelation_equation_1 (A B : Type) (R R' : A -> B -> Prop) :
  Logic.subrelation R R' = forall (x : A) (y : B), R x y -> R' x y.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @subrelation_equation_1 : subrelation.

Arguments Logic.subrelation {_ _} _ _ /.

Corollary unique_equation_1 (A : Type) (P : A -> Prop) (x : A) :
  unique P x = (P x /\ forall x' : A, P x' -> x = x').
Proof. reflexivity. Qed.

#[export] Hint Rewrite @unique_equation_1 : unique.

Arguments unique {_} _ _ /.

Corollary uniqueness_equation_1 (A : Type) (P : A -> Prop) :
  uniqueness P = forall x y : A, P x -> P y -> x = y.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @uniqueness_equation_1 : uniqueness.

Arguments uniqueness {_} _ /.

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

Arguments andb !_ _.
Arguments orb !_ _.
Arguments implb !_ _.
Arguments xorb !_ !_.
Arguments negb !_.
Arguments is_true !_.

(** We might as well treat booleans as reflections of propositions. *)

Coercion is_true : bool >-> Sortclass.

Corollary option_map_equation_1 (A B : Type) (f : A -> B) (x : A) :
  option_map f (Some x) = Some (f x).
Proof. reflexivity. Qed.

Corollary option_map_equation_2 (A B : Type) (f : A -> B) :
  option_map f None = None.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @option_map_equation_1
  @option_map_equation_2 : option_map.

Arguments option_map {_ _} _ !_.

Notation "'_+_'" := sum : type_scope.
Notation "A '+' B" := (sum A B) : type_scope.

Notation "'(_,_)'" := pair : core_scope.
Notation "'(' x ',' y ',' .. ',' z ')'" :=
  (pair .. (pair x y) .. z) : core_scope.

Notation "'_*_'" := prod : type_scope.
Notation "A '*' B" := (prod A B) : type_scope.

Corollary fst_equation_1 (A B : Type) (x : A) (y : B) : fst (x, y) = x.
Proof. reflexivity. Qed.

Corollary snd_equation_1 (A B : Type) (x : A) (y : B) : snd (x, y) = y.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @fst_equation_1 : fst.
#[export] Hint Rewrite @snd_equation_1 : snd.

Arguments fst {_ _} !_.
Arguments snd {_ _} !_.

Corollary length_equation_1 (A : Type) :
  length (A := A) [] = O.
Proof. reflexivity. Qed.

Corollary length_equation_2 (A : Type) (a : A) (l' : list A) :
  length (a :: l') = S (length l').
Proof. reflexivity. Qed.

#[export] Hint Rewrite @length_equation_1 @length_equation_2 : length.

Arguments length {_} !_.

Corollary app_equation_1 (A : Type) (m : list A) :
  [] ++ m = m.
Proof. reflexivity. Qed.

Corollary app_equation_2 (A : Type) (a : A) (l1 m : list A) :
  (a :: l1) ++ m = a :: (l1 ++ m).
Proof. reflexivity. Qed.

#[export] Hint Rewrite @app_equation_1 @app_equation_2 : app.

Arguments app {_} !_ _.

Corollary ID_equation_1 : ID = forall A : Type, A -> A.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @ID_equation_1 : id.

Arguments ID /.

Corollary id_equation_1 (A : Prop) (x : A) : Datatypes.id x = x.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @id_equation_1 : id.

Arguments Datatypes.id {_} _ /.

Notation "'id'" := Datatypes.id : core_scope.

Corollary IDProp_equation_1 : IDProp = forall A : Prop, A -> A.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @IDProp_equation_1 : IDProp.

Arguments IDProp /.

Corollary idProp_equation_1 (A : Prop) (x : A) : idProp x = x.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @idProp_equation_1 : idProp.

Arguments idProp {_} _ /.

(** ** Subsets and Existential Types *)

(** We adjust the implicit arguments of [ex], [sig], [sigT], [Ssig] and
    several other standard library functions to behave the same way. *)

Arguments ex {_} _.
Arguments ex_intro {_} _ _ _.

Declare Scope ex_scope.
Delimit Scope ex_scope with ex.
Bind Scope ex_scope with ex.

Notation "'(_;_)'" := (ex_intro _) : ex_scope.
Notation "'(' x ';' .. ';' y ';' z ')'" :=
  (ex_intro _ x .. (ex_intro _ y z) ..) : ex_scope.

Corollary ex_proj1_equation_1 (A : Prop) (P : A -> Prop) (x : A) (a : P x) :
  ex_proj1 (ex_intro P x a) = x.
Proof. reflexivity. Qed.

Corollary ex_proj2_equation_1 (A : Prop) (P : A -> Prop) (x : A) (a : P x) :
  ex_proj2 (ex_intro P x a) = a.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @ex_proj1_equation_1 : ex_proj1.
#[export] Hint Rewrite @ex_proj2_equation_1 : ex_proj2.

Arguments ex_proj1 {_ _} !_.
Arguments ex_proj2 {_ _} !_.

Arguments sig {_} _.
Arguments exist {_} _ _ _.

Declare Scope sig_scope.
Delimit Scope sig_scope with sig.
Bind Scope sig_scope with sig.

Notation "'(_;_)'" := (exist _) : sig_scope.
Notation "'(' x ';' .. ';' y ';' z ')'" :=
  (exist _ x .. (exist _ y z) ..) : sig_scope.

Notation "'{_|_}'" := sig : type_scope.
Notation "'{' x '|' y '}'" := (sig (fun x : _ => y)) : type_scope.
Notation "'{_:_|_}'" := @sig : type_scope.
Notation "'{' x ':' A '|' y '}'" := (@sig A (fun x : _ => y)) : type_scope.

Corollary proj1_sig_equation_1 (A : Type) (P : A -> Prop) (x : A) (a : P x) :
  proj1_sig (exist P x a) = x.
Proof. reflexivity. Qed.

Corollary proj2_sig_equation_1 (A : Type) (P : A -> Prop) (x : A) (a : P x) :
  proj2_sig (exist P x a) = a.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @proj1_sig_equation_1 : proj1_sig.
#[export] Hint Rewrite @proj2_sig_equation_1 : proj2_sig.

Arguments proj1_sig {_ _} !_.
Arguments proj2_sig {_ _} !_.

Arguments sigT {_} _.
Arguments existT {_} _ _ _.

Declare Scope sigT_scope.
Delimit Scope sigT_scope with sigT.
Bind Scope sigT_scope with sigT.

Notation "'(_;_)'" := (existT _) : sigT_scope.
Notation "'(' x ';' .. ';' y ';' z ')'" :=
  (existT _ x .. (existT _ y z) ..) : sigT_scope.

Notation "'{_&_}'" := sigT : type_scope.
Notation "'{' x '&' y '}'" := (sigT (fun x : _ => y)) : type_scope.
Notation "'{_:_&_}'" := @sigT : type_scope.
Notation "'{' x ':' A '&' y '}'" := (@sigT A (fun x : _ => y)) : type_scope.

Corollary projT1_equation_1 (A : Type) (P : A -> Type) (x : A) (a : P x) :
  projT1 (existT P x a) = x.
Proof. reflexivity. Qed.

Corollary projT2_equation_1 (A : Type) (P : A -> Type) (x : A) (a : P x) :
  projT2 (existT P x a) = a.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @projT1_equation_1 : projT1.
#[export] Hint Rewrite @projT2_equation_1 : projT2.

Arguments projT1 {_ _} !_.
Arguments projT2 {_ _} !_.

Arguments Ssig {_} _.
Arguments Sexists {_} _ _ _.

Declare Scope Ssig_scope.
Delimit Scope Ssig_scope with Ssig.
Bind Scope Ssig_scope with Ssig.

Notation "'(_;_)'" := (Sexists _) : Ssig_scope.
Notation "'(' x ';' .. ';' y ';' z ')'" :=
  (Sexists _ x .. (Sexists _ y z) ..) : Ssig_scope.

(** We should have similar notations for [Ssig] as there are for [sig].
    The mnemonic for [$] in the notation is that it is a combination
    of [|] from the notation for [sig] and [S] from the name of [Ssig].
    Besides, using [!] would conflict with
    the lonely notations of the equations plugin. *)

Notation "'{_$_}'" := Ssig : type_scope.
Notation "'{' x '$' y '}'" := (Ssig (fun x : _ => y)) : type_scope.
Notation "'{_:_$_}'" := @Ssig : type_scope.
Notation "'{' x ':' A '$' y '}'" := (@Ssig A (fun x : _ => y)) : type_scope.

Module StrictProp.

#[local] Set Cumulative StrictProp.

Corollary Spr1_equation_1 (A : Type) (P : A -> SProp) (x : A) (a : P x) :
  Spr1 (Sexists P x a) = x.
Proof. reflexivity. Qed.

Corollary Spr2_equation_1 (A : Type) (P : A -> SProp) (x : A) (a : P x) :
  Spr2 (Sexists P x a) = a.
Proof. reflexivity. Qed.

End StrictProp.

Export StrictProp.

#[export] Hint Rewrite @Spr1_equation_1 : Spr1.
#[export] Hint Rewrite @Spr2_equation_1 : Spr2.

Arguments Spr1 {_ _} !_.
Arguments Spr2 {_ _} !_.

Corollary sig_of_sigT_equation_1 (A : Type) (P : A -> Prop) (x : A) (a : P x) :
  sig_of_sigT (existT P x a) = exist P x a.
Proof. reflexivity. Qed.

Corollary sigT_of_sig_equation_1 (A : Type) (P : A -> Prop) (x : A) (a : P x) :
  sigT_of_sig (exist P x a) = existT P x a.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @sig_of_sigT_equation_1 : sig_of_sigT.
#[export] Hint Rewrite @sigT_of_sig_equation_1 : sigT_of_sig.

Arguments sig_of_sigT {_ _} !_.
Arguments sigT_of_sig {_ _} !_.

(** ** Inspect Pattern *)

(** We explicitly name the inspect pattern
    to make pattern matching with the [with] keyword
    of the equations plugin more readable. *)

Notation "'inspect' x" := (exist _ x eq_refl) (only parsing) : core_scope.
Notation "x 'eqn' ':' a" := (exist _ x a) (only parsing) : core_scope.

(** ** Basic Functions and Combinators *)

(** While some standard library definitions
    need to be overridden with more sensible versions,
    most of them are totally fine,
    in which case we just accompany them with dependent versions. *)

Fail Fail Equations compose (A B C : Type)
  (g : B -> C) (f : A -> B) (x : A) : C :=
  compose g f x := g (f x).

(** Using [o] as a variable name should be prohibited by law,
    which is why we turn it into a notation instead. *)

Notation "'_o_'" := compose : core_scope.
Notation "g 'o' f" := (compose g f) : core_scope.

Corollary compose_equation_1 (A B C : Type)
  (g : B -> C) (f : A -> B) (x : A) :
  (g o f) x = g (f x).
Proof. reflexivity. Qed.

#[export] Hint Rewrite @compose_equation_1 : compose.

Arguments compose {_ _ _} _ _ _ /.

Equations compose_dep
  (A : Type) (P : A -> Type) (S : forall x : A, P x -> Type)
  (g : forall (x : A) (a : P x), S x a) (f : forall x : A, P x)
  (x : A) : S x (f x) :=
  compose_dep g f x := g x (f x).

Arguments compose_dep {_ _ _} _ _ _ /.

(** The equations plugin does not generate subtype lemmas,
    which is why we have to write them by hand. *)

Lemma compose_nondep (A B C : Type) (g : B -> C) (f : A -> B) (x : A) :
  compose_dep (const g) f x = compose g f x.
Proof. reflexivity. Qed.

Fail Fail Equations arrow (A B : Type) : Type :=
  arrow A B := A -> B.

Corollary arrow_equation_1 (A B : Type) : arrow A B = (A -> B).
Proof. reflexivity. Qed.

#[export] Hint Rewrite @arrow_equation_1 : arrow.

Arguments arrow _ _ /.

Fail Fail Equations impl (A B : Prop) : Prop :=
  impl A B := A -> B.

Corollary impl_equation_1 (A B : Prop) : impl A B = (A -> B).
Proof. reflexivity. Qed.

#[export] Hint Rewrite @impl_equation_1 : impl.

Arguments impl _ _ /.

Fail Fail Equations const (A B : Type) (a : A) (b : B) : A :=
  const a b := a.

Corollary const_equation_1 (A B : Type) (a : A) (b : B) : const a b = a.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @const_equation_1 : const.

Arguments const {_ _} _ _ /.

Equations const_dep (A : Type) (P : A -> Type) (a : A) (b : P a) : A :=
  const_dep _ a b := a.

Arguments const_dep {_ _} _ _ /.

Lemma const_nondep (A B : Type) (a : A) (b : B) :
  const_dep a b = const a b.
Proof. reflexivity. Qed.

Fail Fail Equations flip (A B C : Type)
  (f : A -> B -> C) (y : B) (x : A) : C :=
  flip f y x := f x y.

Corollary flip_equation_1 (A B C : Type) (f : A -> B -> C) (x : B) (y : A) :
  flip f x y = f y x.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @flip_equation_1 : flip.

Arguments flip {_ _ _} _ _ _ /.

Equations flip_dep (A B : Type) (P : A -> B -> Type)
  (f : forall (x : A) (y : B), P x y) (y : B) (x : A) : P x y :=
  flip_dep f y x := f x y.

Arguments flip_dep {_ _ _} _ _ _ /.

Lemma flip_nondep (A B C : Type) (f : A -> B -> C) (y : B) (x : A) :
  flip_dep f y x = flip f y x.
Proof. reflexivity. Qed.

Fail Fail Equations apply (A B : Type) (f : A -> B) (x : A) : B :=
  apply f x := f x.

Corollary apply_equation_1 (A B : Type) (f : A -> B) (x : A) :
  apply f x = f x.
Proof. reflexivity. Qed.

#[export] Hint Rewrite @apply_equation_1 : apply.

Arguments apply {_ _} _ _ /.

Equations apply_dep (A : Type) (P : A -> Type)
  (f : forall x : A, P x) (x : A) : P x :=
  apply_dep f x := f x.

Arguments apply_dep {_ _} _ _ /.

Lemma apply_nondep (A B : Type) (f : A -> B) (a : A) :
  apply_dep f a = apply f a.
Proof. reflexivity. Qed.

(** ** Respectful Relations and Morphisms *)

Corollary respectful_equation_1
  (A B : Type) (R : relation A) (R' : relation B) :
  respectful R R' = fun f g : A -> B =>
  forall x y : A, R x y -> R' (f x) (g y).
Proof. reflexivity. Qed.

#[export] Hint Rewrite @respectful_equation_1 : respectful.

Arguments respectful {_ _} _ _ /.

Notation "'_==>_'" := respectful : signature_scope.
Notation "X '==>' Y" := (respectful X Y) : signature_scope.

Corollary respectful_hetero_equation_1
  (A B : Type) (C : A -> Type) (D : B -> Type)
  (R : A -> B -> Prop) (R' : forall (x : A) (y : B), C x -> D y -> Prop) :
  respectful_hetero A B C D R R' =
  fun (f : forall x : A, C x) (g : forall x : B, D x) =>
  forall (x : A) (y : B), R x y -> R' x y (f x) (g y).
Proof. reflexivity. Qed.

#[export] Hint Rewrite @respectful_hetero_equation_1 : respectful_hetero.

Arguments respectful_hetero {_ _ _ _} _ _ /.

Lemma respectful_nondep (A B : Type)
  (X : relation A) (Y : relation B) (f g : A -> B) :
  respectful_hetero X (const (const Y)) f g = respectful X Y f g.
Proof. reflexivity. Qed.

(** ** Currying and Uncurrying *)

(** Currying and uncurrying are swapped around
    in some versions of the standard library and
    not defined for all product types,
    which is why we redefine them all here. *)

Equations conj_curry (A B C : Prop)
  (f : A /\ B -> C) (x : A) (y : B) : C :=
  conj_curry f x y := f (conj x y).

Arguments conj_curry {_ _ _} _ _ _ /.

Equations conj_uncurry (A B C : Prop)
  (f : A -> B -> C) (a : A /\ B) : C :=
  conj_uncurry f (conj x y) := f x y.

Arguments conj_uncurry {_ _ _} _ !_.

Equations ex_curry (A : Prop) (P : A -> Prop) (B : Prop)
  (f : (exists x : A, P x) -> B) (x : A) (a : P x) : B :=
  ex_curry f x a := f (ex_intro P x a).

Arguments ex_curry {_ _ _} _ _ _ /.

Equations ex_curry_dep
  (A : Prop) (P : A -> Prop) (S : forall x : A, P x -> Prop)
  (f : forall a : exists x : A, P x, S (ex_proj1 a) (ex_proj2 a))
  (x : A) (a : P x) : S x a :=
  ex_curry_dep _ f x a := f (ex_intro P x a).

Arguments ex_curry_dep {_ _ _} _ _ _ /.

Lemma ex_curry_nondep (A : Prop) (P : A -> Prop) (B : Prop)
  (f : (exists x : A, P x) -> B) (x : A) (a : P x) :
  ex_curry_dep f x a = ex_curry f x a.
Proof. reflexivity. Qed.

Equations ex_uncurry (A : Prop) (P : A -> Prop) (B : Prop)
  (f : forall x : A, P x -> B) (a : exists x : A, P x) : B :=
  ex_uncurry f (ex_intro _ x a) := f x a.

Arguments ex_uncurry {_ _ _} _ !_.

(** The equations plugin does not generate projection lemmas,
    which is why we have to write them by hand. *)

Lemma ex_uncurry_proj (A : Prop) (P : A -> Prop) (B : Prop)
  (f : forall x : A, P x -> B) (a : exists x : A, P x) :
  ex_uncurry f a = f (ex_proj1 a) (ex_proj2 a).
Proof. destruct a as [x a]. reflexivity. Qed.

Equations ex_uncurry_dep
  (A : Prop) (P : A -> Prop) (S : forall x : A, P x -> Prop)
  (f : forall (x : A) (a : P x), S x a)
  (a : exists x : A, P x) : S (ex_proj1 a) (ex_proj2 a) :=
  ex_uncurry_dep f (ex_intro _ x a) := f x a.

Arguments ex_uncurry_dep {_ _ _} _ !_.

Lemma ex_uncurry_dep_proj
  (A : Prop) (P : A -> Prop) (S : forall x : A, P x -> Prop)
  (f : forall (x : A) (a : P x), S x a)
  (a : exists x : A, P x) :
  ex_uncurry_dep f a = f (ex_proj1 a) (ex_proj2 a).
Proof. destruct a as [x a]. reflexivity. Qed.

Lemma ex_uncurry_nondep (A : Prop) (P : A -> Prop) (B : Prop)
  (f : forall x : A, P x -> B) (a : exists x : A, P x) :
  ex_uncurry_dep f a = ex_uncurry f a.
Proof. destruct a as [x a]. reflexivity. Qed.

Equations prod_curry (A B C : Type)
  (f : A * B -> C) (x : A) (y : B) : C :=
  prod_curry f x y := f (x, y).

Arguments prod_curry {_ _ _} _ _ _ /.

Equations prod_curry_dep (A B : Type) (P : A -> B -> Type)
  (f : forall x : A * B, P (fst x) (snd x)) (x : A) (y : B) : P x y :=
  prod_curry_dep _ f x y := f (x, y).

Arguments prod_curry_dep {_ _ _} _ _ _ /.

Lemma prod_curry_nondep (A B C : Type) (f : A * B -> C) (x : A) (y : B) :
  prod_curry_dep f x y = prod_curry f x y.
Proof. reflexivity. Qed.

Equations prod_uncurry (A B C : Type)
  (f : A -> B -> C) (x : A * B) : C :=
  prod_uncurry f (x, y) := f x y.

Arguments prod_uncurry {_ _ _} _ !_.

Lemma prod_uncurry_proj (A B C : Type)
  (f : A -> B -> C) (a : A * B) :
  prod_uncurry f a = f (fst a) (snd a).
Proof. destruct a as [x y]. reflexivity. Qed.

Equations prod_uncurry_dep (A B : Type) (P : A -> B -> Type)
  (f : forall (x : A) (y : B), P x y) (a : A * B) : P (fst a) (snd a) :=
  prod_uncurry_dep f (x, y) := f x y.

Arguments prod_uncurry_dep {_ _ _} _ !_.

Lemma prod_uncurry_dep_proj (A B : Type) (P : A -> B -> Type)
  (f : forall (x : A) (y : B), P x y) (a : A * B) :
  prod_uncurry_dep f a = f (fst a) (snd a).
Proof. destruct a as [x y]. reflexivity. Qed.

Lemma prod_uncurry_nondep (A B C : Type) (f : A -> B -> C) (a : A * B) :
  prod_uncurry_dep f a = prod_uncurry f a.
Proof. destruct a as [x y]. reflexivity. Qed.

Equations sig_curry (A : Type) (P : A -> Prop) (B : Type)
  (f : {x : A | P x} -> B) (x : A) (a : P x) : B :=
  sig_curry f x a := f (exist P x a).

Arguments sig_curry {_ _ _} _ _ _ /.

Equations sig_curry_dep
  (A : Type) (P : A -> Prop) (S : forall x : A, P x -> Type)
  (f : forall a : {x : A | P x}, S (proj1_sig a) (proj2_sig a))
  (x : A) (a : P x) : S x a :=
  sig_curry_dep _ f x a := f (exist P x a).

Arguments sig_curry_dep {_ _ _} _ _ _ /.

Lemma sig_curry_nondep (A : Type) (P : A -> Prop) (B : Type)
  (f : {x : A | P x} -> B) (x : A) (a : P x) :
  sig_curry_dep f x a = sig_curry f x a.
Proof. reflexivity. Qed.

Equations sig_uncurry (A : Type) (P : A -> Prop) (B : Type)
  (f : forall x : A, P x -> B) (a : {x : A | P x}) : B :=
  sig_uncurry f (exist _ x a) := f x a.

Arguments sig_uncurry {_ _ _} _ !_.

Lemma sig_uncurry_proj (A : Type) (P : A -> Prop) (B : Type)
  (f : forall x : A, P x -> B) (a : {x : A | P x}) :
  sig_uncurry f a = f (proj1_sig a) (proj2_sig a).
Proof. destruct a as [x a]. reflexivity. Qed.

Equations sig_uncurry_dep
  (A : Type) (P : A -> Prop) (S : forall x : A, P x -> Type)
  (f : forall (x : A) (a : P x), S x a)
  (a : {x : A | P x}) : S (proj1_sig a) (proj2_sig a) :=
  sig_uncurry_dep f (exist _ x a) := f x a.

Arguments sig_uncurry_dep {_ _ _} _ !_.

Lemma sig_uncurry_dep_proj
  (A : Type) (P : A -> Prop) (S : forall x : A, P x -> Type)
  (f : forall (x : A) (a : P x), S x a)
  (a : {x : A | P x}) :
  sig_uncurry_dep f a = f (proj1_sig a) (proj2_sig a).
Proof. destruct a as [x a]. reflexivity. Qed.

Lemma sig_uncurry_nondep (A : Type) (P : A -> Prop) (B : Type)
  (f : forall x : A, P x -> B) (a : {x : A | P x}) :
  sig_uncurry_dep f a = sig_uncurry f a.
Proof. destruct a as [x a]. reflexivity. Qed.

Equations sigT_curry (A : Type) (P : A -> Type) (B : Type)
  (f : {x : A & P x} -> B) (x : A) (a : P x) : B :=
  sigT_curry f x a := f (existT P x a).

Arguments sigT_curry {_ _ _} _ _ _ /.

Equations sigT_curry_dep
  (A : Type) (P : A -> Type) (S : forall x : A, P x -> Type)
  (f : forall a : {x : A & P x}, S (projT1 a) (projT2 a))
  (x : A) (a : P x) : S x a :=
  sigT_curry_dep _ f x a := f (existT P x a).

Arguments sigT_curry_dep {_ _ _} _ _ _ /.

Lemma sigT_curry_nondep (A : Type) (P : A -> Type) (B : Type)
  (f : {x : A & P x} -> B) (x : A) (a : P x) :
  sigT_curry_dep f x a = sigT_curry f x a.
Proof. reflexivity. Qed.

Equations sigT_uncurry (A : Type) (P : A -> Type) (B : Type)
  (f : forall x : A, P x -> B) (a : {x : A & P x}) : B :=
  sigT_uncurry f (existT _ x a) := f x a.

Arguments sigT_uncurry {_ _ _} _ !_.

Lemma sigT_uncurry_proj (A : Type) (P : A -> Type) (B : Type)
  (f : forall x : A, P x -> B) (a : {x : A & P x}) :
  sigT_uncurry f a = f (projT1 a) (projT2 a).
Proof. destruct a as [x a]. reflexivity. Qed.

Equations sigT_uncurry_dep
  (A : Type) (P : A -> Type) (S : forall x : A, P x -> Type)
  (f : forall (x : A) (a : P x), S x a)
  (a : {x : A & P x}) : S (projT1 a) (projT2 a) :=
  sigT_uncurry_dep f (existT _ x a) := f x a.

Arguments sigT_uncurry_dep {_ _ _} _ !_.

Lemma sigT_uncurry_dep_proj
  (A : Type) (P : A -> Type) (S : forall x : A, P x -> Type)
  (f : forall (x : A) (a : P x), S x a)
  (a : {x : A & P x}) :
  sigT_uncurry_dep f a = f (projT1 a) (projT2 a).
Proof. destruct a as [x a]. reflexivity. Qed.

Lemma sigT_uncurry_nondep (A : Type) (P : A -> Type) (B : Type)
  (f : forall x : A, P x -> B) (a : {x : A & P x}) :
  sigT_uncurry_dep f a = sigT_uncurry f a.
Proof. destruct a as [x a]. reflexivity. Qed.

Equations Ssig_curry (A : Type) (P : A -> SProp) (B : Type)
  (f : {x : A $ P x} -> B) (x : A) (a : P x) : B :=
  Ssig_curry f x a := f (Sexists P x a).

Arguments Ssig_curry {_ _ _} _ _ _ /.

Equations Ssig_curry_dep
  (A : Type) (P : A -> SProp) (S : forall x : A, P x -> Type)
  (f : forall a : {x : A $ P x}, S (Spr1 a) (Spr2 a))
  (x : A) (a : P x) : S x a :=
  Ssig_curry_dep _ f x a := f (Sexists P x a).

Arguments Ssig_curry_dep {_ _ _} _ _ _ /.

Lemma Ssig_curry_nondep (A : Type) (P : A -> SProp) (B : Type)
  (f : {x : A $ P x} -> B) (x : A) (a : P x) :
  Ssig_curry_dep f x a = Ssig_curry f x a.
Proof. reflexivity. Qed.

Equations Ssig_uncurry (A : Type) (P : A -> SProp) (B : Type)
  (f : forall x : A, P x -> B) (a : {x : A $ P x}) : B :=
  Ssig_uncurry f (Sexists _ x a) := f x a.

Arguments Ssig_uncurry {_ _ _} _ !_.

Lemma Ssig_uncurry_proj (A : Type) (P : A -> SProp) (B : Type)
  (f : forall x : A, P x -> B) (a : {x : A $ P x}) :
  Ssig_uncurry f a = f (Spr1 a) (Spr2 a).
Proof. destruct a as [x a]. reflexivity. Qed.

Equations Ssig_uncurry_dep
  (A : Type) (P : A -> SProp) (S : forall x : A, P x -> Type)
  (f : forall (x : A) (a : P x), S x a)
  (a : {x : A $ P x}) : S (Spr1 a) (Spr2 a) :=
  Ssig_uncurry_dep f (Sexists _ x a) := f x a.

Arguments Ssig_uncurry_dep {_ _ _} _ !_.

Lemma Ssig_uncurry_dep_proj
  (A : Type) (P : A -> SProp) (S : forall x : A, P x -> Type)
  (f : forall (x : A) (a : P x), S x a)
  (a : {x : A $ P x}) :
  Ssig_uncurry_dep f a = f (Spr1 a) (Spr2 a).
Proof. destruct a as [x a]. reflexivity. Qed.

Lemma Ssig_uncurry_nondep (A : Type) (P : A -> SProp) (B : Type)
  (f : forall x : A, P x -> B) (a : {x : A $ P x}) :
  Ssig_uncurry_dep f a = Ssig_uncurry f a.
Proof. destruct a as [x a]. reflexivity. Qed.

(** ** Opacity and Transparency *)

(** Flip these switches and push those carts
    to make unification smart. *)

#[export] Typeclasses Opaque iff all Logic.subrelation unique uniqueness.

#[export] Typeclasses Transparent andb orb implb xorb negb is_true
  option_map fst snd length app ID Datatypes.id IDProp idProp.

#[export] Typeclasses Transparent ex_proj1 ex_proj2 proj1_sig proj2_sig
  projT1 projT2 Spr1 Spr2 sig_of_sigT sigT_of_sig.

#[export] Typeclasses Transparent compose compose_dep arrow impl
  const const_dep flip flip_dep apply apply_dep.

#[export] Typeclasses Transparent conj_curry conj_uncurry
  ex_curry ex_curry_dep ex_uncurry ex_uncurry_dep
  prod_curry prod_curry_dep prod_uncurry prod_uncurry_dep
  sig_curry sig_curry_dep sig_uncurry sig_uncurry_dep
  sigT_curry sigT_curry_dep sigT_uncurry sigT_uncurry_dep
  Ssig_curry Ssig_curry_dep Ssig_uncurry Ssig_uncurry_dep.
