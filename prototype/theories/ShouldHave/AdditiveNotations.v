From Maniunfold.Has Require Export
  ExternalBinaryOperation BinaryOperation Unit.

Delimit Scope algebra_scope with algebra.

Open Scope algebra_scope.

Reserved Notation "a '<+' x" (at level 50, no associativity).
Reserved Notation "x '+>' a" (at level 50, no associativity).

Notation "a '<+' x" := (ex_bi_op a x) : algebra_scope.
Notation "x '+>' a" := (ex_bi_op a x) : algebra_scope.
Notation "x '+' y" := (bi_op x y) : algebra_scope.
Notation "'0'" := un : algebra_scope.
