From Maniunfold.Has Require Export
  GroupOperation GroupIdentity GroupInverse.
From Maniunfold.ShouldHave Require Export
  EquivalenceNotations.

Delimit Scope group_scope with group.

Open Scope group_scope.

Notation "x '+' y" := (opr x y) : group_scope.
Notation "'0'" := idn : group_scope.
Notation "'-' x" := (inv x) : group_scope.
Notation "x '-' y" := (opr x (inv y)) : group_scope.
