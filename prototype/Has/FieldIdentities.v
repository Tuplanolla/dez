From Maniunfold.Has Require Export
  GroupOperation GroupIdentity FieldOperations.

Class HasZero (A : Type) : Type := zero : A.
Class HasOne (A : Type) : Type := one : A.

Typeclasses Transparent HasZero HasOne.

Notation "'0'" := zero : field_scope.
Notation "'1'" := one : field_scope.

Global Instance zero_has_idn {A : Type} {has_zero : HasZero A} : HasIdn A := zero.
Global Instance one_has_idn {A : Type} {has_one : HasOne A} : HasIdn A := one.

(** Numeral notations do not work with type classes,
    so we need to construct each notation from repeated additions.
    The following automatically generated construction
    produces an optimal reduction tree (one of many). *)

Section Context.

Context {A : Type} {has_add : HasAdd A} {has_one : HasOne A}.

Definition two : A := add one one.
Definition three : A := add two one.
Definition four : A := add two two.
Definition five : A := add four one.
Definition six : A := add four two.
Definition seven : A := add four three.
Definition eight : A := add four four.
Definition nine : A := add eight one.

End Context.

Notation "'2'" := two : field_scope.
Notation "'3'" := three : field_scope.
Notation "'4'" := four : field_scope.
Notation "'5'" := five : field_scope.
Notation "'6'" := six : field_scope.
Notation "'7'" := seven : field_scope.
Notation "'8'" := eight : field_scope.
Notation "'9'" := nine : field_scope.
