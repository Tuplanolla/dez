From Maniunfold.Has Require Export
  OneSorted.OrderRelation.

Declare Scope algebra_scope.

Delimit Scope algebra_scope with algebra.

Open Scope algebra_scope.

Reserved Notation "x '<=' y" (at level 70, no associativity).
Notation "x '<=' y" := (ord_rel x y) : algebra_scope.
