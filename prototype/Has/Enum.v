(** TODO Consider using a universal property over a concrete list. *)

Class HasEnum (A : Type) : Type := enum : list A.

Typeclasses Transparent HasEnum.
