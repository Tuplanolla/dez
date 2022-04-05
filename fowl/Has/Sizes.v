(** * Sizes *)

From Coq Require Import
  NArith.NArith.
From DEZ Require Export
  Init.

(** ** Cardinality *)
(** ** Size *)

Class HasSize (A : Type) : Type := size : N.

Arguments size _ {_}.

#[export] Typeclasses Transparent HasSize.
