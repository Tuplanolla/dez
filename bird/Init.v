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
