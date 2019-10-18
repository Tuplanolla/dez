From Maniunfold.Has Require Import
  GroupOperation GroupIdentity FieldOperations.

Class HasZero (A : Type) : Type := zero : A.
Class HasOne (A : Type) : Type := one : A.

Typeclasses Transparent HasZero HasOne.

Notation "'0'" := zero : field_scope.
Notation "'1'" := one : field_scope.

Instance zero_has_idn {A : Type} {has_zero : HasZero A} : HasIdn A := zero.
Instance one_has_idn {A : Type} {has_one : HasOne A} : HasIdn A := one.

(** Numeral notations do not work with type classes,
    so we need to construct them from additions.
    The following automatically generated construction
    produces an optimal reduction tree (one of many). *)

Definition two {A : Type} {has_add : HasAdd A} {has_one : HasOne A} : A :=
  add one one.
Definition three {A : Type} {has_add : HasAdd A} {has_one : HasOne A} : A :=
  add two one.
Definition four {A : Type} {has_add : HasAdd A} {has_one : HasOne A} : A :=
  add two two.
Definition five {A : Type} {has_add : HasAdd A} {has_one : HasOne A} : A :=
  add four one.
Definition six {A : Type} {has_add : HasAdd A} {has_one : HasOne A} : A :=
  add four two.
Definition seven {A : Type} {has_add : HasAdd A} {has_one : HasOne A} : A :=
  add four three.
Definition eight {A : Type} {has_add : HasAdd A} {has_one : HasOne A} : A :=
  add four four.
Definition nine {A : Type} {has_add : HasAdd A} {has_one : HasOne A} : A :=
  add eight one.

Notation "'2'" := two : field_scope.
Notation "'3'" := three : field_scope.
Notation "'4'" := four : field_scope.
Notation "'5'" := five : field_scope.
Notation "'6'" := six : field_scope.
Notation "'7'" := seven : field_scope.
Notation "'8'" := eight : field_scope.
Notation "'9'" := nine : field_scope.
