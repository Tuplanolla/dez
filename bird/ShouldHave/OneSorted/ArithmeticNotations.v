From Maniunfold.Has Require Export
  Addition Zero Negation Multiplication One Reciprocation.

Declare Scope algebra_scope.

Delimit Scope algebra_scope with algebra.

Open Scope algebra_scope.

Notation "x '+' y" := (add x y) : algebra_scope.
Notation "'0'" := zero : algebra_scope.
Notation "'-' x" := (neg x) : algebra_scope.
Notation "x '*' y" := (mul x y) : algebra_scope.
Notation "'1'" := one : algebra_scope.
Notation "'/' x" := (recip x) : algebra_scope.
