From Maniunfold Require Export
  Init.

(** We do not use the abbreviation [op],
    because it is reserved for dual morphisms. *)

Class HasOpr (A : Type) : Type := opr : A -> A -> A.

Typeclasses Transparent HasOpr.
