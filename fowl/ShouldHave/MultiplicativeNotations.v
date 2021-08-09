(** * Multiplicative Notations for Algebraic Operations *)

From DEZ.Has Require Import
  Torsion Action NullaryOperation UnaryOperation BinaryOperation.

Reserved Notation "x '*<' y" (left associativity, at level 40).
Reserved Notation "x '>*' y" (left associativity, at level 40).
Reserved Notation "x '/<' y" (right associativity, at level 35).
Reserved Notation "x '>/' y" (right associativity, at level 35).

Declare Scope left_torsion_scope.
Delimit Scope left_torsion_scope with tor_l.

(** We do not open chiral scopes,
    because we do not want to favor one over the other. *)

Notation "'_/_'" := tor_l : left_torsion_scope.
Notation "y '/' x" := (tor_l x y) : left_torsion_scope.

Declare Scope right_torsion_scope.
Delimit Scope right_torsion_scope with tor_r.

Notation "'_/_'" := tor_r : right_torsion_scope.
Notation "y '/' x" := (tor_r x y) : right_torsion_scope.

Declare Scope torsion_scope.
Delimit Scope torsion_scope with tor.

#[global] Open Scope torsion_scope.

Notation "'_/<_'" := tor_l : torsion_scope.
Notation "y '/<' x" := (tor_l x y) : torsion_scope.
Notation "'_>/_'" := tor_r : torsion_scope.
Notation "y '>/' x" := (tor_r x y) : torsion_scope.

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
