From Maniunfold Require Export
  Init.

(** Enumeration, listing, collection.
    Commonly found in finite sets. *)

Class HasEnum (A : Type) : Type := enum : list A.

Typeclasses Transparent HasEnum.
