From DEZ.Offers Require Export
  FieldConstants.

(** Numeral notations do not work with type classes,
    which is why we define numerals only up to a single decimal digit. *)

Notation "'2'" := two : field_scope.
Notation "'3'" := three : field_scope.
Notation "'4'" := four : field_scope.
Notation "'5'" := five : field_scope.
Notation "'6'" := six : field_scope.
Notation "'7'" := seven : field_scope.
Notation "'8'" := eight : field_scope.
Notation "'9'" := nine : field_scope.
