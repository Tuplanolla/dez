(** * Multiplicative Notations for Algebraic Operations *)

From DEZ.Has Require Import
  AlgebraicOperations AlgebraicActions.

Reserved Notation "x '*<' y" (left associativity, at level 40).
Reserved Notation "x '>*' y" (left associativity, at level 40).
Reserved Notation "x '/<' y" (right associativity, at level 35).
Reserved Notation "x '>/' y" (right associativity, at level 35).

Declare Scope left_action_scope.
Delimit Scope left_action_scope with act_l.

Notation "'_*_'" := act_l : left_action_scope.
Notation "a '*' x" := (act_l a x) : left_action_scope.

Declare Scope right_action_scope.
Delimit Scope right_action_scope with act_r.

Notation "'_*_'" := act_r : right_action_scope.
Notation "x '*' a" := (act_r x a) : right_action_scope.

Declare Scope action_scope.
Delimit Scope action_scope with act.

#[global] Open Scope action_scope.

Notation "'_*<_'" := act_l : action_scope.
Notation "a '*<' x" := (act_l a x) : action_scope.
Notation "'_>*_'" := act_r : action_scope.
Notation "x '>*' a" := (act_r x a) : action_scope.

Declare Scope operation_scope.
Delimit Scope operation_scope with op.

#[global] Open Scope operation_scope.

Notation "'1'" := null_op : operation_scope.
Notation "'/_'" := un_op : operation_scope.
Notation "'/' x" := (un_op x) : operation_scope.
Notation "'_*_'" := bin_op : operation_scope.
Notation "x '*' y" := (bin_op x y) : operation_scope.
