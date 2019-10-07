From Maniunfold.Has Require Import Operation Identity.

Delimit Scope inverse_scope with inverse.

Open Scope inverse_scope.

Class HasInv (A : Type) : Type := inv : A -> A.

Module AdditiveNotations.

Export Identity.AdditiveNotations.

Notation "'-' x" := (inv x) : inverse_scope.
Notation "x '-' y" := (opr x (inv y)) : inverse_scope.

End AdditiveNotations.

Module MultiplicativeNotations.

Export Identity.MultiplicativeNotations.

Notation "'/' x" := (inv x) : inverse_scope.
Notation "x '/' y" := (opr x (inv y)) : inverse_scope.

End MultiplicativeNotations.
