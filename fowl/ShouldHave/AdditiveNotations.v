From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation UnaryOperation Action Torsion.

Declare Scope operation_scope.
Delimit Scope operation_scope with op.

Notation "'_+_'" := bin_op : op.
Notation "x '+' y" := (bin_op x y) : op.
Notation "'0'" := null_op : op.
Notation "'-_'" := un_op : op.
Notation "'-' x" := (un_op x) : op.

Declare Scope left_action_scope.
Delimit Scope left_action_scope with act_l.

Notation "'_+_'" := act_l : act_l.
Notation "a '+' x" := (act_l a x) : act_l.
Notation "'_-_'" := (fun (a : _) (x : _) => act_l a (un_op x)) : act_l.
Notation "a '-' x" := (act_l a (un_op x)) : act_l.

Declare Scope right_action_scope.
Delimit Scope right_action_scope with act_r.

Notation "'_+_'" := act_r : act_r.
Notation "x '+' a" := (act_r x a) : act_r.
Notation "'_-_'" := (fun (x : _) (a : _) => act_r x (un_op a)) : act_r.
Notation "x '-' a" := (act_r x (un_op a)) : act_r.

Declare Scope left_torsion_scope.
Delimit Scope left_torsion_scope with tor_l.

Notation "'_-_'" := tor_l : tor_l.
Notation "x '-' y" := (tor_l x y) : tor_l.

Declare Scope right_torsion_scope.
Delimit Scope right_torsion_scope with tor_r.

Notation "'_-_'" := tor_l : tor_r.
Notation "x '-' y" := (tor_r x y) : tor_r.

(** We do not open chiral scopes,
    because we do not want to favor one over the other. *)

#[global] Open Scope op.
