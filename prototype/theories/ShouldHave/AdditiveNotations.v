From Maniunfold.Has Require Export
  BinaryOperation Unit UnaryOperation
  LeftExternalBinaryOperation RightExternalBinaryOperation Function
  BinaryFunction.

Delimit Scope algebra_scope with algebra.

Open Scope algebra_scope.

Notation "x '+' y" := (bin_op x y) : algebra_scope.
Notation "'0'" := un : algebra_scope.
Notation "'-' x" := (un_op x) : algebra_scope.
Notation "x '-' y" := (bin_op x (un_op y)) : algebra_scope.

Reserved Notation "x '+<' y" (at level 50, left associativity).
Reserved Notation "x '>+' y" (at level 50, left associativity).
Reserved Notation "'>-<' x" (at level 35, right associativity).
Reserved Notation "x '-<' y" (at level 50, left associativity).
Reserved Notation "x '>-' y" (at level 50, left associativity).

Notation "x '+<' y" := (l_ext_bin_op x y) : algebra_scope.
Notation "x '>+' y" := (r_ext_bin_op x y) : algebra_scope.
Notation "'>-<' x" := (fn x) : algebra_scope.
Notation "x '-<' y" := (l_ext_bin_op x (fn y)) : algebra_scope.
Notation "x '>-' y" := (r_ext_bin_op x (fn y)) : algebra_scope.

Reserved Notation "x '>+<' y" (at level 50, left associativity).
Reserved Notation "x '>-<' y" (at level 50, left associativity).

Notation "x '>+<' y" := (bin_fn x y) : algebra_scope.
Notation "x '>-<' y" := (bin_fn x (fn y)) : algebra_scope.
