From DEZ.Has Require Export
  Power.

Delimit Scope exponential_scope with exponential.

Open Scope exponential_scope.

Notation "x '^' y" := (pow x y) : exponential_scope.
