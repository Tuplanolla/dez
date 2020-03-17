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

Tactic Notation "typeclasses" "specialize"
  uconstr(x0) "into" uconstr(y0) :=
  change x0 with y0 in *.

(** TODO There ought to be a better way to define this tactic recursively. *)

(** These were generated with the following Haskell program.

<<
f c d = "Tactic Notation \"typeclasses\" \"specialize\"" <> mconcat
  (intersperse " \"or\"" [mconcat
    (intersperse " \"and\"" ["\n  uconstr(x" <> show i <> "x" <> show j <>
      ") \"into\" uconstr(y" <> show i <> "y" <> show j <> ")" |
      i <- [1 .. c]]) | j <- [1 .. d]]) <> " :=" <> mconcat
  (intersperse "||" [" (" <> mconcat
    (intersperse ";" ["\n  change x" <> show i <> "x" <> show j <>
      " with y" <> show i <> "y" <> show j <> " in *" |
      i <- [1 .. c]]) <> ") " | j <- [1 .. d]]) <>
  "||\n  fail \"Failed to specialize\".\n"
k = putStr (mconcat (intersperse "\n" [f c d | d <- [1 .. 4], c <- [1 .. 4]]))
>> *)

Tactic Notation "typeclasses" "specialize"
  uconstr(x1x1) "into" uconstr(y1y1) := (
  change x1x1 with y1y1 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x2x1) "into" uconstr(y2y1) := (
  change x1x1 with y1y1 in *;
  change x2x1 with y2y1 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "and"
  uconstr(x3x1) "into" uconstr(y3y1) := (
  change x1x1 with y1y1 in *;
  change x2x1 with y2y1 in *;
  change x3x1 with y3y1 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "and"
  uconstr(x3x1) "into" uconstr(y3y1) "and"
  uconstr(x4x1) "into" uconstr(y4y1) := (
  change x1x1 with y1y1 in *;
  change x2x1 with y2y1 in *;
  change x3x1 with y3y1 in *;
  change x4x1 with y4y1 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x1x1) "into" uconstr(y1y1) "or"
  uconstr(x1x2) "into" uconstr(y1y2) := (
  change x1x1 with y1y1 in *) || (
  change x1x2 with y1y2 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "or"
  uconstr(x1x2) "into" uconstr(y1y2) "and"
  uconstr(x2x2) "into" uconstr(y2y2) := (
  change x1x1 with y1y1 in *;
  change x2x1 with y2y1 in *) || (
  change x1x2 with y1y2 in *;
  change x2x2 with y2y2 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "and"
  uconstr(x3x1) "into" uconstr(y3y1) "or"
  uconstr(x1x2) "into" uconstr(y1y2) "and"
  uconstr(x2x2) "into" uconstr(y2y2) "and"
  uconstr(x3x2) "into" uconstr(y3y2) := (
  change x1x1 with y1y1 in *;
  change x2x1 with y2y1 in *;
  change x3x1 with y3y1 in *) || (
  change x1x2 with y1y2 in *;
  change x2x2 with y2y2 in *;
  change x3x2 with y3y2 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "and"
  uconstr(x3x1) "into" uconstr(y3y1) "and"
  uconstr(x4x1) "into" uconstr(y4y1) "or"
  uconstr(x1x2) "into" uconstr(y1y2) "and"
  uconstr(x2x2) "into" uconstr(y2y2) "and"
  uconstr(x3x2) "into" uconstr(y3y2) "and"
  uconstr(x4x2) "into" uconstr(y4y2) := (
  change x1x1 with y1y1 in *;
  change x2x1 with y2y1 in *;
  change x3x1 with y3y1 in *;
  change x4x1 with y4y1 in *) || (
  change x1x2 with y1y2 in *;
  change x2x2 with y2y2 in *;
  change x3x2 with y3y2 in *;
  change x4x2 with y4y2 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x1x1) "into" uconstr(y1y1) "or"
  uconstr(x1x2) "into" uconstr(y1y2) "or"
  uconstr(x1x3) "into" uconstr(y1y3) := (
  change x1x1 with y1y1 in *) || (
  change x1x2 with y1y2 in *) || (
  change x1x3 with y1y3 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "or"
  uconstr(x1x2) "into" uconstr(y1y2) "and"
  uconstr(x2x2) "into" uconstr(y2y2) "or"
  uconstr(x1x3) "into" uconstr(y1y3) "and"
  uconstr(x2x3) "into" uconstr(y2y3) := (
  change x1x1 with y1y1 in *;
  change x2x1 with y2y1 in *) || (
  change x1x2 with y1y2 in *;
  change x2x2 with y2y2 in *) || (
  change x1x3 with y1y3 in *;
  change x2x3 with y2y3 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "and"
  uconstr(x3x1) "into" uconstr(y3y1) "or"
  uconstr(x1x2) "into" uconstr(y1y2) "and"
  uconstr(x2x2) "into" uconstr(y2y2) "and"
  uconstr(x3x2) "into" uconstr(y3y2) "or"
  uconstr(x1x3) "into" uconstr(y1y3) "and"
  uconstr(x2x3) "into" uconstr(y2y3) "and"
  uconstr(x3x3) "into" uconstr(y3y3) := (
  change x1x1 with y1y1 in *;
  change x2x1 with y2y1 in *;
  change x3x1 with y3y1 in *) || (
  change x1x2 with y1y2 in *;
  change x2x2 with y2y2 in *;
  change x3x2 with y3y2 in *) || (
  change x1x3 with y1y3 in *;
  change x2x3 with y2y3 in *;
  change x3x3 with y3y3 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "and"
  uconstr(x3x1) "into" uconstr(y3y1) "and"
  uconstr(x4x1) "into" uconstr(y4y1) "or"
  uconstr(x1x2) "into" uconstr(y1y2) "and"
  uconstr(x2x2) "into" uconstr(y2y2) "and"
  uconstr(x3x2) "into" uconstr(y3y2) "and"
  uconstr(x4x2) "into" uconstr(y4y2) "or"
  uconstr(x1x3) "into" uconstr(y1y3) "and"
  uconstr(x2x3) "into" uconstr(y2y3) "and"
  uconstr(x3x3) "into" uconstr(y3y3) "and"
  uconstr(x4x3) "into" uconstr(y4y3) := (
  change x1x1 with y1y1 in *;
  change x2x1 with y2y1 in *;
  change x3x1 with y3y1 in *;
  change x4x1 with y4y1 in *) || (
  change x1x2 with y1y2 in *;
  change x2x2 with y2y2 in *;
  change x3x2 with y3y2 in *;
  change x4x2 with y4y2 in *) || (
  change x1x3 with y1y3 in *;
  change x2x3 with y2y3 in *;
  change x3x3 with y3y3 in *;
  change x4x3 with y4y3 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x1x1) "into" uconstr(y1y1) "or"
  uconstr(x1x2) "into" uconstr(y1y2) "or"
  uconstr(x1x3) "into" uconstr(y1y3) "or"
  uconstr(x1x4) "into" uconstr(y1y4) := (
  change x1x1 with y1y1 in *) || (
  change x1x2 with y1y2 in *) || (
  change x1x3 with y1y3 in *) || (
  change x1x4 with y1y4 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "or"
  uconstr(x1x2) "into" uconstr(y1y2) "and"
  uconstr(x2x2) "into" uconstr(y2y2) "or"
  uconstr(x1x3) "into" uconstr(y1y3) "and"
  uconstr(x2x3) "into" uconstr(y2y3) "or"
  uconstr(x1x4) "into" uconstr(y1y4) "and"
  uconstr(x2x4) "into" uconstr(y2y4) := (
  change x1x1 with y1y1 in *;
  change x2x1 with y2y1 in *) || (
  change x1x2 with y1y2 in *;
  change x2x2 with y2y2 in *) || (
  change x1x3 with y1y3 in *;
  change x2x3 with y2y3 in *) || (
  change x1x4 with y1y4 in *;
  change x2x4 with y2y4 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "and"
  uconstr(x3x1) "into" uconstr(y3y1) "or"
  uconstr(x1x2) "into" uconstr(y1y2) "and"
  uconstr(x2x2) "into" uconstr(y2y2) "and"
  uconstr(x3x2) "into" uconstr(y3y2) "or"
  uconstr(x1x3) "into" uconstr(y1y3) "and"
  uconstr(x2x3) "into" uconstr(y2y3) "and"
  uconstr(x3x3) "into" uconstr(y3y3) "or"
  uconstr(x1x4) "into" uconstr(y1y4) "and"
  uconstr(x2x4) "into" uconstr(y2y4) "and"
  uconstr(x3x4) "into" uconstr(y3y4) := (
  change x1x1 with y1y1 in *;
  change x2x1 with y2y1 in *;
  change x3x1 with y3y1 in *) || (
  change x1x2 with y1y2 in *;
  change x2x2 with y2y2 in *;
  change x3x2 with y3y2 in *) || (
  change x1x3 with y1y3 in *;
  change x2x3 with y2y3 in *;
  change x3x3 with y3y3 in *) || (
  change x1x4 with y1y4 in *;
  change x2x4 with y2y4 in *;
  change x3x4 with y3y4 in *) ||
  fail "Failed to specialize".

Tactic Notation "typeclasses" "specialize"
  uconstr(x1x1) "into" uconstr(y1y1) "and"
  uconstr(x2x1) "into" uconstr(y2y1) "and"
  uconstr(x3x1) "into" uconstr(y3y1) "and"
  uconstr(x4x1) "into" uconstr(y4y1) "or"
  uconstr(x1x2) "into" uconstr(y1y2) "and"
  uconstr(x2x2) "into" uconstr(y2y2) "and"
  uconstr(x3x2) "into" uconstr(y3y2) "and"
  uconstr(x4x2) "into" uconstr(y4y2) "or"
  uconstr(x1x3) "into" uconstr(y1y3) "and"
  uconstr(x2x3) "into" uconstr(y2y3) "and"
  uconstr(x3x3) "into" uconstr(y3y3) "and"
  uconstr(x4x3) "into" uconstr(y4y3) "or"
  uconstr(x1x4) "into" uconstr(y1y4) "and"
  uconstr(x2x4) "into" uconstr(y2y4) "and"
  uconstr(x3x4) "into" uconstr(y3y4) "and"
  uconstr(x4x4) "into" uconstr(y4y4) := (
  change x1x1 with y1y1 in *;
  change x2x1 with y2y1 in *;
  change x3x1 with y3y1 in *;
  change x4x1 with y4y1 in *) || (
  change x1x2 with y1y2 in *;
  change x2x2 with y2y2 in *;
  change x3x2 with y3y2 in *;
  change x4x2 with y4y2 in *) || (
  change x1x3 with y1y3 in *;
  change x2x3 with y2y3 in *;
  change x3x3 with y3y3 in *;
  change x4x3 with y4y3 in *) || (
  change x1x4 with y1y4 in *;
  change x2x4 with y2y4 in *;
  change x3x4 with y3y4 in *;
  change x4x4 with y4y4 in *) ||
  fail "Failed to specialize".
