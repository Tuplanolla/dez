(** We disable universe polymorphism until we really need it,
    because it is experimental and comes with a performance penalty. *)

Global Unset Universe Polymorphism.

(** We disable warnings about overriding notations,
    because the plan is to replace many basic notations like [<=] and [+]. *)

Global Set Warnings "-notation-overridden".

(** We export [Basics] to make its utility functions available everywhere,
    import [Morphisms] to gain access to [signature_scope] and
    import [Setoid] to strengthen the [rewrite] tactic. *)

From Coq Require Export
  Program.Basics.
From Coq Require Import
  Classes.Morphisms Classes.CMorphisms.
From Coq Require Import
  Setoids.Setoid.

(** We mark the utility functions from [Basics] transparent for unification. *)

Typeclasses Transparent compose arrow impl const flip apply.

(** We open [signature_scope] to be able to use [=>] anywhere. *)

Open Scope signature_scope.
