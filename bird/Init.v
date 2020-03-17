(** We disable universe polymorphism until we really need it,
    because it is experimental and comes with a performance penalty. *)

Global Unset Universe Polymorphism.

(** We disable warnings about overriding notations,
    because the plan is to replace many basic notations like [<=] and [+]. *)

Global Set Warnings "-notation-overridden".

(** We export [Basics] to make its utility functions available everywhere,
    import [Logic] to gain access to the [EqNotations] submodule and
    import [Setoid] to generalize the [rewrite] tactic. *)

From Coq Require Export
  Program.Basics.
From Coq Require Import
  Init.Logic.
From Coq Require Import
  Setoids.Setoid.

(** We mark the utility functions from [Basics] transparent for unification. *)

Typeclasses Transparent compose arrow impl const flip apply.

(** We export the [rew] notations to use them like a transport lemma. *)

Export EqNotations.

(** We define the following to conveniently specialize into subclasses. *)

(** TODO There ought to be a better way to define this tactic recursively. *)

Tactic Notation "typeclasses" "specialize"
  uconstr(x0) "into" uconstr(y0) :=
  change x0 with y0 in *.

Tactic Notation "typeclasses" "specialize"
  uconstr(x0) "into" uconstr(y0) ","
  uconstr(x1) "into" uconstr(y1) :=
  change x0 with y0 in *;
  change x1 with y1 in *.

Tactic Notation "typeclasses" "specialize"
  uconstr(x0) "into" uconstr(y0) ","
  uconstr(x1) "into" uconstr(y1) ","
  uconstr(x2) "into" uconstr(y2) :=
  change x0 with y0 in *;
  change x1 with y1 in *;
  change x2 with y2 in *.

Tactic Notation "typeclasses" "specialize"
  uconstr(x0) "into" uconstr(y0) ","
  uconstr(x1) "into" uconstr(y1) ","
  uconstr(x2) "into" uconstr(y2) ","
  uconstr(x3) "into" uconstr(y3) :=
  change x0 with y0 in *;
  change x1 with y1 in *;
  change x2 with y2 in *;
  change x3 with y3 in *.
