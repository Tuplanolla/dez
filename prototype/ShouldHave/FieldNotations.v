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

Notation "'2'" := two : field_scope.
Notation "'3'" := three : field_scope.
Notation "'4'" := four : field_scope.
Notation "'5'" := five : field_scope.
Notation "'6'" := six : field_scope.
Notation "'7'" := seven : field_scope.
Notation "'8'" := eight : field_scope.
Notation "'9'" := nine : field_scope.
