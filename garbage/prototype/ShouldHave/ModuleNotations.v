From DEZ.Has Require Export
  ScalarMultiplication.
From DEZ.ShouldHave Require Export
  EquivalenceNotations.

Delimit Scope module_scope with module.

Open Scope module_scope.

Reserved Notation "a '<*' x" (at level 40, left associativity).
Notation "a '<*' x" := (lsmul a x) : module_scope.

Reserved Notation "x '*>' a" (at level 40, left associativity).
Notation "x '*>' a" := (rsmul a x) : module_scope.
