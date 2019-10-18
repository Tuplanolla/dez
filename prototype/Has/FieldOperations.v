From Maniunfold.Has Require Import
  GroupOperation.

Delimit Scope field_scope with field.

Open Scope field_scope.

Class HasAdd (A : Type) : Type := add : A -> A -> A.
Class HasMul (A : Type) : Type := mul : A -> A -> A.

Typeclasses Transparent HasAdd HasMul.

Notation "x '+' y" := (add x y) : field_scope.
Notation "x '*' y" := (mul x y) : field_scope.

Section Context.

Context {A : Type} {has_add : HasAdd A}.

Global Instance : HasOpr A := add.

End Context.

Section Context.

Context {A : Type} {has_mul : HasMul A}.

Global Instance : HasOpr A := mul.

End Context.
