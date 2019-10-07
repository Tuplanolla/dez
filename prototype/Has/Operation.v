Delimit Scope operation_scope with operation.

Open Scope operation_scope.

(** We do not use the abbreviation [op],
    because it is reserved for dual morphisms. *)
Class HasOpr (A : Type) : Type := opr : A -> A -> A.

Module AdditiveNotations.

Notation "x '+' y" := (opr x y) : operation_scope.

End AdditiveNotations.

Module MultiplicativeNotations.

Notation "x '*' y" := (opr x y) : operation_scope.

End MultiplicativeNotations.
