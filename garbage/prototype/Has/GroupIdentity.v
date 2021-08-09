From DEZ.Has Require Export
  GroupOperation.

(** We do not use the abbreviation [id],
    because it is reserved for identity morphisms. *)

Class HasIdn (A : Type) : Type := idn : A.

Typeclasses Transparent HasIdn.
