From Coq Require Import
  NArith.NArith.
From Maniunfold.Has Require Export
  TwoSorted.LeftAction.
From Maniunfold.Is Require Import
  OneSorted.Monoid.
From Maniunfold.Offers Require Export
  OneSorted.PositiveOperations.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

(** TODO Split operation notations. *)

Local Reserved Notation "n '*' x" (at level 40, left associativity).
Local Reserved Notation "x '^' n" (at level 30, right associativity).

Local Reserved Notation "'_*_'" (at level 0, no associativity).
Local Reserved Notation "'_^_'" (at level 0, no associativity).

Local Notation "n '*' x" := (positive_op _+_ n x) : positive_scope.
Local Notation "'_*_'" := (positive_op _+_) (only parsing) : positive_scope.

Section Context.

Context (A : Type) `{IsMon A}.

Fixpoint nat_op (n : nat) (x : A) : A :=
  match n with
  | O => 0
  | S p => x + @nat_op p x
  end.

Global Instance nat_A_has_l_act : HasLAct nat A := nat_op.

Definition n_op (n : N) (x : A) : A :=
  match n with
  | N0 => 0
  | Npos p => (p * x)%positive
  end.

Global Instance N_A_has_l_act : HasLAct N A := n_op.

End Context.

Arguments nat_op {_} _ _ !_ _.
Arguments n_op {_} _ _ !_ _.
