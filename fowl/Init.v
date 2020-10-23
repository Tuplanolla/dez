(** We disable warnings about overriding notations,
    because the plan is to replace many basic notations like [<=] and [+]. *)

Global Set Warnings "-notation-overridden".

(** We turn on automatically inferred implicit arguments and
    make them maximally inserted and conservatively detected,
    since most type classes follow the same design pattern. *)

Global Set Implicit Arguments.
Global Set Maximal Implicit Insertion.
Global Set Strict Implicit.
Global Set Strongly Strict Implicit.
Global Unset Contextual Implicit.
Global Unset Reversible Pattern Implicit.

(** We disable universe polymorphism until we really need it,
    because it is experimental and
    incurs a considerable performance penalty on type checking. *)

Global Unset Universe Polymorphism.

(** We export [Datatypes] and [Basics] to
    make their utility functions available everywhere,
    import [Logic] to gain access to the [EqNotations] submodule and
    import [Setoid] to generalize the [rewrite] tactic. *)

From Coq Require Export
  Init.Datatypes Program.Basics.
From Coq Require Import
  Init.Logic.
From Coq Require Import
  Setoids.Setoid.

(** We do not use implicit generalization,
    because the consequences of accidental misuse
    are worse than the convenience it permits. *)

Global Generalizable No Variables.

(** We do not allow automatic solution of obligations,
    because we do not want the addition or removal of hints
    to change the total number of obligations. *)

Obligation Tactic := idtac.

(** Using [o] as a variable name should be prohibited by law,
    which is why we turn it into a notation. *)

Reserved Notation "g 'o' f" (at level 40, left associativity).

Notation "g 'o' f" := (compose g f) : core_scope.

(** We define some additional utility functions. *)

Definition sig_uncurry {A : Type} {P : A -> Prop} {C : Type}
  (f : {x : A | P x} -> C) (x : A) (y : P x) : C :=
  f (exist P x y).

Definition sig_curry {A : Type} {P : A -> Prop} {C : Type}
  (f : forall x : A, P x -> C) (xy : {x : A | P x}) : C :=
  f (proj1_sig xy) (proj2_sig xy).

Definition sigT_uncurry {A : Type} {P : A -> Type} {C : Type}
  (f : {x : A & P x} -> C) (x : A) (y : P x) : C :=
  f (existT P x y).

Definition sigT_curry {A : Type} {P : A -> Type} {C : Type}
  (f : forall x : A, P x -> C) (xy : {x : A & P x}) : C :=
  f (projT1 xy) (projT2 xy).

(** We mark the utility functions transparent for unification and
    provide some hints for simplifying them. *)

Typeclasses Transparent andb orb implb xorb negb is_true option_map fst snd
  prod_uncurry prod_curry length app ID id IDProp idProp.

Typeclasses Transparent compose arrow impl const flip apply.

Typeclasses Transparent sig_uncurry sig_curry sigT_uncurry sigT_curry.

Arguments andb !_ _.
Arguments orb !_ _.
Arguments implb !_ _.
Arguments xorb !_ !_.
Arguments negb !_.
Arguments is_true !_.
Arguments option_map {_ _} _ !_.
Arguments fst {_ _} !_.
Arguments snd {_ _} !_.
Arguments prod_uncurry {_ _ _} _ _ _ /.
Arguments prod_curry {_ _ _} _ !_.
Arguments length {_} !_.
Arguments app {_} !_ _.
Arguments ID /.
Arguments id _ _ /.
Arguments IDProp /.
Arguments idProp _ _ /.

Arguments compose {_ _ _} _ _ _ /.
Arguments arrow _ _ /.
Arguments impl _ _ /.
Arguments const {_ _} _ _ /.
Arguments flip {_ _ _} _ _ _ /.
Arguments apply {_ _} _ _ /.

Arguments sig_uncurry {_ _ _} _ _ _ /.
Arguments sig_curry {_ _ _} _ !_.
Arguments sigT_uncurry {_ _ _} _ _ _ /.
Arguments sigT_curry {_ _ _} _ !_.

(** We only use obligations to define local lemmas,
    which is why we do not want to see them in search results. *)

Add Search Blacklist "_obligation_".

(** We export the [rew] notations to use them like a transport lemma. *)

Export EqNotations.

(** We define the following tactic notations
    to conveniently specialize superclasses into subclasses.
    There are more principled ways to do this,
    but they all require plugins or other more advanced mechanisms. *)

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
