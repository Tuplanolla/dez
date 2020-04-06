From Coq Require Import
  NArith.NArith.
From Maniunfold Require Export
  Init.

(** Cardinality, size, measure, numerosity.
    Commonly found in finite sets. *)

Class HasCard (A : Type) : Type := card : N.

Arguments card : clear implicits.
Arguments card _ {_}.

Typeclasses Transparent HasCard.
