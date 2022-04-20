(** * Cardinalities *)

From Coq Require Import
  NArith.NArith.
From DEZ Require Export
  Init.

(** ** Finite Cardinality *)
(** ** Finite Size *)

Class HasFinCard (A : Type) : Type := fin_card : N.

Arguments fin_card _ {_}.

#[export] Typeclasses Transparent HasFinCard.
