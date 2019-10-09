From Maniunfold.Has Require Import GroupOperation.

Delimit Scope field_scope with field.

Open Scope field_scope.

Class HasAdd (A : Type) : Type := add : A -> A -> A.
Class HasMul (A : Type) : Type := mul : A -> A -> A.

Notation "x '+' y" := (add x y) : field_scope.
Notation "x '*' y" := (mul x y) : field_scope.

Instance add_has_opr {A : Type} {has_add : HasAdd A} : HasOpr A := add.
Instance mul_has_opr {A : Type} {has_mul : HasMul A} : HasOpr A := mul.
