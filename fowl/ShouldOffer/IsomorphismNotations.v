From Maniunfold.Has Require Export
  Isomorphism.

Declare Scope iso_scope.

Delimit Scope iso_scope with iso.

Open Scope iso_scope.

Reserved Notation "'_~=_'" (no associativity, at level 0).
Reserved Notation "A '~=' B" (no associativity, at level 70).

Notation "'_~=_'" := iso : iso_scope.
Notation "A '~=' B" := (iso A B) : iso_scope.
