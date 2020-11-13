From Maniunfold.Has Require Export
  OneSorted.Join OneSorted.Bottom OneSorted.Meet OneSorted.Top.

Declare Scope lat_scope.

Delimit Scope lat_scope with lat.

Open Scope lat_scope.

Notation "x '\/' y" := (join x y) : lat_scope.
Notation "'_|_'" := bot : lat_scope.
Notation "x '/\' y" := (meet x y) : lat_scope.
Notation "'-|-'" := top : lat_scope.

Notation "'_\/_'" := join (only parsing) : lat_scope.
Notation "'_/\_'" := meet (only parsing) : lat_scope.
