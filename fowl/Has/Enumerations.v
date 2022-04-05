(** * Enumerations *)

From Coq Require Import
  Lists.List.
From DEZ Require Export
  Init.

(** ** Unsorted Enumeration *)

Class HasEnum (A : Type) : Type := enum : list A.

Arguments enum _ {_}.

#[export] Typeclasses Transparent HasEnum.
