From Maniunfold.Has Require Export
  BinaryOperation Unit UnaryOperation
  BinaryFunction LeftUnit RightUnit
  LeftExternalBinaryOperation RightExternalBinaryOperation Function (* TODO Chiral functions? *)
  BinaryFunction Function.

Declare Scope algebra_scope.

Delimit Scope algebra_scope with algebra.

Open Scope algebra_scope.

Notation "x '+' y" := (bin_op x y) : algebra_scope.
Notation "'0'" := un : algebra_scope.
Notation "'-' x" := (un_op x) : algebra_scope.
Notation "x '-' y" := (bin_op x (un_op y)) : algebra_scope.

Reserved Notation "x '+<' y" (at level 50, left associativity).
Reserved Notation "x '>+' y" (at level 50, left associativity).
Reserved Notation "'0<'" (at level 0, no associativity).
Reserved Notation "'>0'" (at level 0, no associativity).
Reserved Notation "'-<' x" (at level 35, right associativity).
Reserved Notation "'>-' x" (at level 35, right associativity).

Notation "x '+<' y" := (l_ext_bin_op x y) : algebra_scope.
Notation "x '>+' y" := (r_ext_bin_op x y) : algebra_scope.
Notation "'0<'" := l_un : algebra_scope.
Notation "'>0'" := r_un : algebra_scope.
Notation "'-<' x" := (fn x) : algebra_scope.
Notation "'>-' x" := (fn x) : algebra_scope.

Reserved Notation "x '>+<' y" (at level 50, left associativity).
Reserved Notation "'>-<' x" (at level 35, right associativity).

Notation "x '>+<' y" := (bin_fn x y) : algebra_scope.
Notation "'>-<' x" := (fn x) : algebra_scope.
