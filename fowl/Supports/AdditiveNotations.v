(** * Additive Notations for Algebraic Operations *)

From Coq Require Import
  ZArith.ZArith.
From DEZ.Has Require Import
  Operations Actions.

(** Some programming languages like Octave
    use [.+] and [.*] for scalar operations,
    but we cannot do that due to [.] being the command terminator.
    Other programming languages like Haskell
    use [<+] and [<*] for chiral operations,
    but we cannot do that due to [->] being the function arrow. *)

Reserved Notation "x '+<' y" (left associativity, at level 50).
Reserved Notation "x '>+' y" (left associativity, at level 50).
Reserved Notation "x '-<' y" (right associativity, at level 35).
Reserved Notation "x '>-' y" (right associativity, at level 35).

Declare Scope left_action_scope.
Delimit Scope left_action_scope with act_l.

Notation "'_+_'" := act_l : left_action_scope.
Notation "a '+' x" := (act_l a x) : left_action_scope.

Declare Scope right_action_scope.
Delimit Scope right_action_scope with act_r.

Notation "'_+_'" := act_r : right_action_scope.
Notation "x '+' a" := (act_r x a) : right_action_scope.

Declare Scope action_scope.
Delimit Scope action_scope with act.

#[global] Open Scope action_scope.

Notation "'_+<_'" := act_l : action_scope.
Notation "a '+<' x" := (act_l a x) : action_scope.
Notation "'_>+_'" := act_r : action_scope.
Notation "x '>+' a" := (act_r x a) : action_scope.

Declare Scope operation_scope.
Delimit Scope operation_scope with op.

#[global] Open Scope operation_scope.

Notation "'-_'" := un_op : operation_scope.
Notation "'-' x" := (un_op x) : operation_scope.
Notation "'_+_'" := bin_op : operation_scope.
Notation "x '+' y" := (bin_op x y) : operation_scope.

Module Reified.

Equations unit_of_Z (n : Z) : option unit :=
  unit_of_Z Z0 := Some tt;
  unit_of_Z _ := None.

Equations Z_of_unit (x : unit) : option Z :=
  Z_of_unit _ := Some Z0.

Module Notations.

#[local] Set Warnings "-numbers".

Context (A : Type) {x : HasNullOp A}.

Number Notation A unit_of_Z Z_of_unit (via unit mapping [
  [null_op] => tt]) : operation_scope.

End Notations.

End Reified.

Export Reified.Notations.
