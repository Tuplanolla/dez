(** We disable universe polymorphism,
    because it is known to be inconsistent. *)

Global Unset Universe Polymorphism.

(** We disable warnings about notation overriding,
    since we override many basic notations like [<=] and [+]. *)

Global Set Warnings "-notation-overridden".

(** We export [Basics] to make its utility functions available everywhere and
    import [Morphisms] to gain access to [signature_scope]. *)

From Coq Require Export
  Basics.
From Coq Require Import
  Morphisms.

(** We mark the utility functions from [Basics] transparent for unification. *)

Typeclasses Transparent compose arrow impl const flip apply.

(** We open [signature_scope] to be able to use [==>] anywhere. *)

Open Scope signature_scope.
