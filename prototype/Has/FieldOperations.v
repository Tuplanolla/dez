From Maniunfold.Has Require Export
  GroupOperation.

Delimit Scope field_scope with field.

Open Scope field_scope.

Class HasAdd (A : Type) : Type := add : A -> A -> A.
Class HasMul (A : Type) : Type := mul : A -> A -> A.

Typeclasses Transparent HasAdd HasMul.

Notation "x '+' y" := (add x y) : field_scope.
Notation "x '*' y" := (mul x y) : field_scope.

Global Instance add_has_opr {A : Type} {has_add : HasAdd A} : HasOpr A := add.
Global Instance mul_has_opr {A : Type} {has_mul : HasMul A} : HasOpr A := mul.
