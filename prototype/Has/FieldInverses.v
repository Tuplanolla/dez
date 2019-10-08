From Maniunfold.Has Require Import FieldOperations FieldIdentities.

Class HasNeg (A : Type) : Type := neg : A -> A.
Class HasRecip (A : Type) : Type := recip : A -> A.

Notation "'-' x" := (neg x) : field_scope.
Notation "x '-' y" := (add x (neg y)) : field_scope.
Notation "'/' x" := (recip x) : field_scope.
Notation "x '/' y" := (mul x (recip y)) : field_scope.
