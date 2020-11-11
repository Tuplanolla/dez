From Coq Require Import
  ZArith.ZArith.
From Maniunfold.Has Require Export
  TwoSorted.LeftAction.
From Maniunfold.Is Require Import
  OneSorted.Group.
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

Context (A : Type) `{IsGrp A}.

Definition z_op (n : Z) (x : A) : A :=
  match n with
  | Z0 => 0
  | Zpos p => (p * x)%positive
  | Zneg p => - (p * x)%positive
  end.

Global Instance Z_A_has_l_act : HasLAct Z A := z_op.

End Context.

Arguments z_op {_} _ _ _ !_ _.
