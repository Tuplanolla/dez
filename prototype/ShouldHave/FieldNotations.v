From Maniunfold.Has Require Export
  FieldOperations FieldIdentities FieldInverses.
From Maniunfold.ShouldHave Require Export
  EquivalenceNotations.

Delimit Scope field_scope with field.

Open Scope field_scope.

Notation "x '+' y" := (add x y) : field_scope.
Notation "x '*' y" := (mul x y) : field_scope.
Notation "'0'" := zero : field_scope.
Notation "'1'" := one : field_scope.
Notation "x '-' y" := (add x (neg y)) : field_scope.
Notation "x '/' y" := (mul x (recip y)) : field_scope.
