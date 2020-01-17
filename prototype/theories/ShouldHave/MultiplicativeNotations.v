From Maniunfold.Has Require Export
  BinaryOperation Unit EndoFunction
  LeftExternalBinaryOperation RightExternalBinaryOperation Function.

Delimit Scope algebra_scope with algebra.

Open Scope algebra_scope.

Notation "x '*' y" := (bi_op x y) : algebra_scope.
Notation "'1'" := un : algebra_scope.
Notation "'/' x" := (endo_fn x) : algebra_scope.
Notation "x '/' y" := (bi_op x (endo_fn y)) : algebra_scope.
