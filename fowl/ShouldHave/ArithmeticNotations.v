(** * Additive and Multiplicative Notations for Algebraic Operations *)

From Maniunfold.Has Require Export
  Addition Negation Zero Multiplication Reciprocation One ScalarMultiplication.

Reserved Notation "x ',*' y" (left associativity, at level 40).
Reserved Notation "x '*,' y" (left associativity, at level 40).

Declare Scope arithmetic_scope.
Delimit Scope arithmetic_scope with arith.

(** We do not open chiral scopes,
    because we do not want to favor one over the other. *)

#[global] Open Scope arithmetic_scope.

Notation "'_+_'" := add : arithmetic_scope.
Notation "x '+' y" := (add x y) : arithmetic_scope.
Notation "'-_'" := neg : arithmetic_scope.
Notation "'-' x" := (neg x) : arithmetic_scope.
Notation "'0'" := zero : arithmetic_scope.
Notation "'_*_'" := mul : arithmetic_scope.
Notation "x '*' y" := (mul x y) : arithmetic_scope.
Notation "'/_'" := recip : arithmetic_scope.
Notation "'/' x" := (recip x) : arithmetic_scope.
Notation "'1'" := one : arithmetic_scope.
Notation "'_,*_'" := s_mul_l : arithmetic_scope.
Notation "a ',*' x" := (s_mul_l a x) : arithmetic_scope.
Notation "'_*,_'" := s_mul_r : arithmetic_scope.
Notation "x '*,' a" := (s_mul_r x a) : arithmetic_scope.
