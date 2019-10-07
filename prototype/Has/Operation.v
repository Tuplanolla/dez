Delimit Scope semigroup_scope with semigroup.

Open Scope semigroup_scope.

(** We do not use the abbreviation [op],
    because it is reserved for dual morphisms. *)
Class HasOpr (A : Type) : Type := opr : A -> A -> A.

Module AdditiveNotations.

Notation "x '+' y" := (opr x y) : semigroup_scope.

End AdditiveNotations.

Module MultiplicativeNotations.

Notation "x '*' y" := (opr x y) : semigroup_scope.

End MultiplicativeNotations.

Import AdditiveNotations.
