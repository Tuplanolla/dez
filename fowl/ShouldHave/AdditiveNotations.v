From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation UnaryOperation Action Torsion.

Declare Scope operation_scope.
Delimit Scope operation_scope with op.

(** We do not open chiral scopes,
    because we do not want to favor one over the other. *)

#[global] Open Scope operation_scope.

Notation "'_+_'" := bin_op : operation_scope.
Notation "x '+' y" := (bin_op x y) : operation_scope.
Notation "'0'" := null_op : operation_scope.
Notation "'-_'" := un_op : operation_scope.
Notation "'-' x" := (un_op x) : operation_scope.

Declare Scope left_action_scope.
Delimit Scope left_action_scope with act_l.

Notation "'_+_'" := act_l : left_action_scope.
Notation "a '+' x" := (act_l a x) : left_action_scope.

Declare Scope right_action_scope.
Delimit Scope right_action_scope with act_r.

Notation "'_+_'" := act_r : right_action_scope.
Notation "x '+' a" := (act_r x a) : right_action_scope.

Declare Scope left_torsion_scope.
Delimit Scope left_torsion_scope with tor_l.

Notation "'_-_'" := tor_l : left_torsion_scope.
Notation "x '-' y" := (tor_l x y) : left_torsion_scope.

Declare Scope right_torsion_scope.
Delimit Scope right_torsion_scope with tor_r.

Notation "'_-_'" := tor_l : right_torsion_scope.
Notation "x '-' y" := (tor_r x y) : right_torsion_scope.
