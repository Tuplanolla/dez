From Maniunfold.Has Require Import Operation.

Delimit Scope identity_scope with identity.

Open Scope identity_scope.

(** We do not use the abbreviation [id],
    because it is reserved for identity morphisms. *)
Class HasIdn (A : Type) : Type := idn : A.

Module AdditiveNotations.

Export Operation.AdditiveNotations.

Notation "'0'" := idn : identity_scope.

End AdditiveNotations.

Module MultiplicativeNotations.

Export Operation.MultiplicativeNotations.

Notation "'1'" := idn : identity_scope.

End MultiplicativeNotations.
