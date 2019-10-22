From Maniunfold.Has Require Export
  GroupOperation GroupIdentity GroupInverse.
(* From Maniunfold.Justifies Require Export
  IntegerPowers. *)
From Maniunfold.Supports Require Export
  EquivalenceNotations.

Delimit Scope group_scope with group.

Open Scope group_scope.

Notation "x '*' y" := (opr x y) : group_scope.
Notation "'1'" := idn : group_scope.
Notation "'/' x" := (inv x) : group_scope.
Notation "x '/' y" := (opr x (inv y)) : group_scope.

(* Notation "x '^' n" := (popr n x) : positive_scope.
Notation "x '^' n" := (nopr n x) : N_scope.
Notation "x '^' n" := (zopr n x) : Z_scope. *)
