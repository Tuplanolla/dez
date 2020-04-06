(** We disable warnings about overriding notations,
    because the plan is to replace many basic notations like [<=] and [+]. *)

Global Set Warnings "-notation-overridden".

(** We disable universe polymorphism until we really need it,
    because it is experimental and comes with a performance penalty. *)

Global Unset Universe Polymorphism.

(** We export [Basics] to make its utility functions available everywhere,
    import [Logic] to gain access to the [EqNotations] submodule and
    import [Setoid] to generalize the [rewrite] tactic. *)

From Coq Require Export
  Program.Basics.
From Coq Require Import
  Init.Logic.
From Coq Require Import
  Setoids.Setoid.

(** We define some additional utility functions. *)

Definition curry {A B C : Type} (f : A * B -> C) (x : A) (y : B) : C :=
  f (x, y).

Definition uncurry {A B C : Type} (f : A -> B -> C) (xy : A * B) : C :=
  f (fst xy) (snd xy).

(** We mark the utility functions transparent for unification. *)

Typeclasses Transparent compose arrow impl const flip apply.
Typeclasses Transparent curry uncurry.

(** We export the [rew] notations to use them like a transport lemma. *)

Export EqNotations.

(** We define the following to conveniently specialize into subclasses. *)

Tactic Notation "typeclasses" "specialize"
  uconstr(x0) "into" uconstr(y0) :=
  change x0 with y0 in *.

(** TODO There ought to be a better way to define this tactic recursively. *)

(** These were generated with the following Haskell program.

<<
import Control.Monad (replicateM)
import Data.List (intersperse)

f d cs = "Tactic Notation \"typeclasses\" \"specialize\"" <> mconcat
  (intersperse " \"or\"" [mconcat
    (intersperse " \"and\"" ["\n  uconstr(x" <> show i <> "x" <> show j <>
      ") \"into\" uconstr(y" <> show i <> "y" <> show j <> ")" |
      j <- [0 .. pred (cs !! i)]]) | i <- [0 .. pred d]]) <> " :=" <> mconcat
  (intersperse "||" [" (" <> mconcat
    (intersperse ";" ["\n  change x" <> show i <> "x" <> show j <>
      " with y" <> show i <> "y" <> show j <> " in *" |
      j <- [0 .. pred (cs !! i)]]) <> ") " | i <- [0 .. pred d]]) <>
  "||\n  fail \"Failed to specialize\".\n"
k n = putStr (mconcat (intersperse "\n" [mconcat (intersperse "\n" [f d cs |
    cs <- replicateM d [1 .. n]]) | d <- [1 .. n]]))
>> *)

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) := (
  change x0x0 with y0y0 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "and"
  uconstr(x0x2) "into" uconstr(y0y2) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *;
  change x0x2 with y0y2 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "or"
  uconstr(x1x0) "into" uconstr(y1y0) := (
  change x0x0 with y0y0 in *) || (
  change x1x0 with y1y0 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) := (
  change x0x0 with y0y0 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x1x2) "into" uconstr(y1y2) := (
  change x0x0 with y0y0 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *;
  change x1x2 with y1y2 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "or"
  uconstr(x1x0) "into" uconstr(y1y0) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *) || (
  change x1x0 with y1y0 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x1x2) "into" uconstr(y1y2) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *;
  change x1x2 with y1y2 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "and"
  uconstr(x0x2) "into" uconstr(y0y2) "or"
  uconstr(x1x0) "into" uconstr(y1y0) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *;
  change x0x2 with y0y2 in *) || (
  change x1x0 with y1y0 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "and"
  uconstr(x0x2) "into" uconstr(y0y2) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *;
  change x0x2 with y0y2 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "and"
  uconstr(x0x2) "into" uconstr(y0y2) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x1x2) "into" uconstr(y1y2) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *;
  change x0x2 with y0y2 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *;
  change x1x2 with y1y2 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "or"
  uconstr(x2x0) "into" uconstr(y2y0) := (
  change x0x0 with y0y0 in *) || (
  change x1x0 with y1y0 in *) || (
  change x2x0 with y2y0 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "or"
  uconstr(x2x0) "into" uconstr(y2y0) "and"
  uconstr(x2x1) "into" uconstr(y2y1) := (
  change x0x0 with y0y0 in *) || (
  change x1x0 with y1y0 in *) || (
  change x2x0 with y2y0 in *;
  change x2x1 with y2y1 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "or"
  uconstr(x2x0) "into" uconstr(y2y0) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "and"
  uconstr(x2x2) "into" uconstr(y2y2) := (
  change x0x0 with y0y0 in *) || (
  change x1x0 with y1y0 in *) || (
  change x2x0 with y2y0 in *;
  change x2x1 with y2y1 in *;
  change x2x2 with y2y2 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "or"
  uconstr(x2x0) "into" uconstr(y2y0) := (
  change x0x0 with y0y0 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *) || (
  change x2x0 with y2y0 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "or"
  uconstr(x2x0) "into" uconstr(y2y0) "and"
  uconstr(x2x1) "into" uconstr(y2y1) := (
  change x0x0 with y0y0 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *) || (
  change x2x0 with y2y0 in *;
  change x2x1 with y2y1 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "or"
  uconstr(x2x0) "into" uconstr(y2y0) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "and"
  uconstr(x2x2) "into" uconstr(y2y2) := (
  change x0x0 with y0y0 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *) || (
  change x2x0 with y2y0 in *;
  change x2x1 with y2y1 in *;
  change x2x2 with y2y2 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x1x2) "into" uconstr(y1y2) "or"
  uconstr(x2x0) "into" uconstr(y2y0) := (
  change x0x0 with y0y0 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *;
  change x1x2 with y1y2 in *) || (
  change x2x0 with y2y0 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x1x2) "into" uconstr(y1y2) "or"
  uconstr(x2x0) "into" uconstr(y2y0) "and"
  uconstr(x2x1) "into" uconstr(y2y1) := (
  change x0x0 with y0y0 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *;
  change x1x2 with y1y2 in *) || (
  change x2x0 with y2y0 in *;
  change x2x1 with y2y1 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x1x2) "into" uconstr(y1y2) "or"
  uconstr(x2x0) "into" uconstr(y2y0) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "and"
  uconstr(x2x2) "into" uconstr(y2y2) := (
  change x0x0 with y0y0 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *;
  change x1x2 with y1y2 in *) || (
  change x2x0 with y2y0 in *;
  change x2x1 with y2y1 in *;
  change x2x2 with y2y2 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "or"
  uconstr(x2x0) "into" uconstr(y2y0) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *) || (
  change x1x0 with y1y0 in *) || (
  change x2x0 with y2y0 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "or"
  uconstr(x2x0) "into" uconstr(y2y0) "and"
  uconstr(x2x1) "into" uconstr(y2y1) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *) || (
  change x1x0 with y1y0 in *) || (
  change x2x0 with y2y0 in *;
  change x2x1 with y2y1 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "or"
  uconstr(x2x0) "into" uconstr(y2y0) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "and"
  uconstr(x2x2) "into" uconstr(y2y2) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *) || (
  change x1x0 with y1y0 in *) || (
  change x2x0 with y2y0 in *;
  change x2x1 with y2y1 in *;
  change x2x2 with y2y2 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "or"
  uconstr(x2x0) "into" uconstr(y2y0) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *) || (
  change x2x0 with y2y0 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "or"
  uconstr(x2x0) "into" uconstr(y2y0) "and"
  uconstr(x2x1) "into" uconstr(y2y1) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *) || (
  change x2x0 with y2y0 in *;
  change x2x1 with y2y1 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "or"
  uconstr(x2x0) "into" uconstr(y2y0) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "and"
  uconstr(x2x2) "into" uconstr(y2y2) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *) || (
  change x2x0 with y2y0 in *;
  change x2x1 with y2y1 in *;
  change x2x2 with y2y2 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x1x2) "into" uconstr(y1y2) "or"
  uconstr(x2x0) "into" uconstr(y2y0) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *;
  change x1x2 with y1y2 in *) || (
  change x2x0 with y2y0 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x1x2) "into" uconstr(y1y2) "or"
  uconstr(x2x0) "into" uconstr(y2y0) "and"
  uconstr(x2x1) "into" uconstr(y2y1) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *;
  change x1x2 with y1y2 in *) || (
  change x2x0 with y2y0 in *;
  change x2x1 with y2y1 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x1x2) "into" uconstr(y1y2) "or"
  uconstr(x2x0) "into" uconstr(y2y0) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "and"
  uconstr(x2x2) "into" uconstr(y2y2) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *;
  change x1x2 with y1y2 in *) || (
  change x2x0 with y2y0 in *;
  change x2x1 with y2y1 in *;
  change x2x2 with y2y2 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "and"
  uconstr(x0x2) "into" uconstr(y0y2) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "or"
  uconstr(x2x0) "into" uconstr(y2y0) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *;
  change x0x2 with y0y2 in *) || (
  change x1x0 with y1y0 in *) || (
  change x2x0 with y2y0 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "and"
  uconstr(x0x2) "into" uconstr(y0y2) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "or"
  uconstr(x2x0) "into" uconstr(y2y0) "and"
  uconstr(x2x1) "into" uconstr(y2y1) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *;
  change x0x2 with y0y2 in *) || (
  change x1x0 with y1y0 in *) || (
  change x2x0 with y2y0 in *;
  change x2x1 with y2y1 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "and"
  uconstr(x0x2) "into" uconstr(y0y2) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "or"
  uconstr(x2x0) "into" uconstr(y2y0) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "and"
  uconstr(x2x2) "into" uconstr(y2y2) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *;
  change x0x2 with y0y2 in *) || (
  change x1x0 with y1y0 in *) || (
  change x2x0 with y2y0 in *;
  change x2x1 with y2y1 in *;
  change x2x2 with y2y2 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "and"
  uconstr(x0x2) "into" uconstr(y0y2) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "or"
  uconstr(x2x0) "into" uconstr(y2y0) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *;
  change x0x2 with y0y2 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *) || (
  change x2x0 with y2y0 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "and"
  uconstr(x0x2) "into" uconstr(y0y2) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "or"
  uconstr(x2x0) "into" uconstr(y2y0) "and"
  uconstr(x2x1) "into" uconstr(y2y1) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *;
  change x0x2 with y0y2 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *) || (
  change x2x0 with y2y0 in *;
  change x2x1 with y2y1 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "and"
  uconstr(x0x2) "into" uconstr(y0y2) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "or"
  uconstr(x2x0) "into" uconstr(y2y0) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "and"
  uconstr(x2x2) "into" uconstr(y2y2) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *;
  change x0x2 with y0y2 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *) || (
  change x2x0 with y2y0 in *;
  change x2x1 with y2y1 in *;
  change x2x2 with y2y2 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "and"
  uconstr(x0x2) "into" uconstr(y0y2) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x1x2) "into" uconstr(y1y2) "or"
  uconstr(x2x0) "into" uconstr(y2y0) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *;
  change x0x2 with y0y2 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *;
  change x1x2 with y1y2 in *) || (
  change x2x0 with y2y0 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "and"
  uconstr(x0x2) "into" uconstr(y0y2) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x1x2) "into" uconstr(y1y2) "or"
  uconstr(x2x0) "into" uconstr(y2y0) "and"
  uconstr(x2x1) "into" uconstr(y2y1) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *;
  change x0x2 with y0y2 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *;
  change x1x2 with y1y2 in *) || (
  change x2x0 with y2y0 in *;
  change x2x1 with y2y1 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x0x0) "into" uconstr(y0y0) "and"
  uconstr(x0x1) "into" uconstr(y0y1) "and"
  uconstr(x0x2) "into" uconstr(y0y2) "or"
  uconstr(x1x0) "into" uconstr(y1y0) "and"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x1x2) "into" uconstr(y1y2) "or"
  uconstr(x2x0) "into" uconstr(y2y0) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "and"
  uconstr(x2x2) "into" uconstr(y2y2) := (
  change x0x0 with y0y0 in *;
  change x0x1 with y0y1 in *;
  change x0x2 with y0y2 in *) || (
  change x1x0 with y1y0 in *;
  change x1x1 with y1y1 in *;
  change x1x2 with y1y2 in *) || (
  change x2x0 with y2y0 in *;
  change x2x1 with y2y1 in *;
  change x2x2 with y2y2 in *) ||
  fail "Failed to specialize".
