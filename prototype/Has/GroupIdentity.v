From Maniunfold.Has Require Import
  GroupOperation.

Delimit Scope group_scope with group.

Open Scope group_scope.

(** We do not use the abbreviation [id],
    because it is reserved for identity morphisms. *)

Class HasIdn (A : Type) : Type := idn : A.

Typeclasses Transparent HasIdn.

Module AdditiveNotations.

Export GroupOperation.AdditiveNotations.

Notation "'0'" := idn : group_scope.

End AdditiveNotations.

Module MultiplicativeNotations.

Export GroupOperation.MultiplicativeNotations.

Notation "'1'" := idn : group_scope.

End MultiplicativeNotations.
