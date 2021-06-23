From Maniunfold.Has Require Import
  Addition Zero Multiplication One.

Declare Scope lat_scope.

Delimit Scope lat_scope with lat.

Open Scope lat_scope.

Notation "'_\/_'" := add : lat_scope.
Notation "x '\/' y" := (add x y) : lat_scope.
Notation "'_|_'" := zero : lat_scope.
Notation "'_/\_'" := mul : lat_scope.
Notation "x '/\' y" := (mul x y) : lat_scope.
Notation "'-|-'" := one : lat_scope.
