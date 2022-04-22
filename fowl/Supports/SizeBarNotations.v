(** * Vertical Bar Notations for Cardinalities of Types *)

From DEZ.Has Require Import
  Cardinalities.

Declare Scope card_scope.
Delimit Scope card_scope with card.

Notation "'|_|'" := card : card_scope.
Notation "'|' A '|'" := (card A) (format "'|' A '|'") : card_scope.
