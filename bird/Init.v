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
