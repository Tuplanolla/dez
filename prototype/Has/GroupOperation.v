Delimit Scope group_scope with group.

Open Scope group_scope.

(** We do not use the abbreviation [op],
    because it is reserved for dual morphisms. *)
Class HasOpr (A : Type) : Type := opr : A -> A -> A.

Module AdditiveNotations.

Notation "x '+' y" := (opr x y) : group_scope.

End AdditiveNotations.

Module MultiplicativeNotations.

Notation "x '*' y" := (opr x y) : group_scope.

End MultiplicativeNotations.
