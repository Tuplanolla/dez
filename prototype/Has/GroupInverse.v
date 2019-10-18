From Maniunfold.Has Require Import
  Endomorphism GroupOperation GroupIdentity.

Delimit Scope group_scope with group.

Open Scope group_scope.

Class HasInv (A : Type) : Type := inv : A -> A.

Typeclasses Transparent HasInv.

Module AdditiveNotations.

Export GroupIdentity.AdditiveNotations.

Notation "'-' x" := (inv x) : group_scope.
Notation "x '-' y" := (opr x (inv y)) : group_scope.

End AdditiveNotations.

Module MultiplicativeNotations.

Export GroupIdentity.MultiplicativeNotations.

Notation "'/' x" := (inv x) : group_scope.
Notation "x '/' y" := (opr x (inv y)) : group_scope.

End MultiplicativeNotations.

Instance inv_has_endo {A : Type} {has_inv : HasInv A} : HasEndo A := inv.
