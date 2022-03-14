From DEZ.Has Require Import
  ArithmeticOperations.

Declare Scope ring_scope.

Delimit Scope ring_scope with ring.

Open Scope ring_scope.

Notation "x '+' y" := (add x y) : ring_scope.
Notation "'0'" := zero : ring_scope.
Notation "'-' x" := (neg x) : ring_scope.
Notation "x '*' y" := (mul x y) : ring_scope.
Notation "'1'" := one : ring_scope.
Notation "'/' x" := (recip x) : ring_scope.

Notation "'_+_'" := add (only parsing) : ring_scope.
Notation "'-_'" := neg (only parsing) : ring_scope.
Notation "'_*_'" := mul (only parsing) : ring_scope.
Notation "'/_'" := recip (only parsing) : ring_scope.
