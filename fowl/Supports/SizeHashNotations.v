(** * Hash Notations for Cardinalities of Types *)

From DEZ.Has Require Import
  Cardinalities.

Reserved Notation "'#' A" (right associativity, at level 35).

Declare Scope card_scope.
Delimit Scope card_scope with card.

Notation "'#_'" := card : card_scope.
Notation "'#' A" := (card A) (format "'#' A") : card_scope.
