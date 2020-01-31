From Maniunfold.Has Require Export
  BinaryOperation Unit UnaryOperation
  BinaryFunction LeftUnit RightUnit
  LeftExternalBinaryOperation RightExternalBinaryOperation
  LeftFunction RightFunction BinaryFunction Function.

Declare Scope algebra_scope.

Delimit Scope algebra_scope with algebra.

Open Scope algebra_scope.

Notation "x '+' y" := (bin_op x y) : algebra_scope.
Notation "'0'" := un : algebra_scope.
Notation "'-' x" := (un_op x) : algebra_scope.

(** Using [0L] would be a syntax error, which is why we use [L0]. *)

Reserved Notation "x 'L+' y" (at level 50, left associativity).
Reserved Notation "x 'R+' y" (at level 50, left associativity).
Reserved Notation "'L0'" (at level 0, no associativity).
Reserved Notation "'R0'" (at level 0, no associativity).
Reserved Notation "'L-' x" (at level 35, right associativity).
Reserved Notation "'R-' x" (at level 35, right associativity).

Notation "x 'L+' y" := (l_ext_bin_op x y) : algebra_scope.
Notation "x 'R+' y" := (r_ext_bin_op x y) : algebra_scope.
Notation "'L0'" := l_un : algebra_scope.
Notation "'R0'" := r_un : algebra_scope.
Notation "'L-' x" := (l_fn x) : algebra_scope.
Notation "'R-' x" := (r_fn x) : algebra_scope.

(** Using [T0] without restrictions would shadow [0],
    so we make it apply to [only parsing].
    The [T] itself comes from the term two-sided. *)

Reserved Notation "x 'T+' y" (at level 50, left associativity).
Reserved Notation "'T0'" (at level 0, no associativity).
Reserved Notation "'T-' x" (at level 35, right associativity).

Notation "x 'T+' y" := (bin_fn x y) : algebra_scope.
Notation "'T0'" := un (only parsing) : algebra_scope.
Notation "'T-' x" := (fn x) : algebra_scope.
