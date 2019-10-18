From Maniunfold Require Export
  Init.

Delimit Scope module_scope with module.

Open Scope module_scope.

Class HasLSMul (S A : Type) : Type := lsmul : S -> A -> A.
Class HasRSMul (S A : Type) : Type := rsmul : S -> A -> A.

Reserved Notation "a '<*' x" (at level 45, left associativity).
Notation "a '<*' x" := (lsmul a x) : module_scope.

Reserved Notation "x '*>' a" (at level 45, left associativity).
Notation "x '*>' a" := (rsmul a x) : module_scope.

Typeclasses Transparent HasLSMul HasRSMul.
