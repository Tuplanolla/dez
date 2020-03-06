From Maniunfold.Has Require Export
  OneSorted.Join OneSorted.Bottom OneSorted.Meet OneSorted.Top.

Declare Scope algebra_scope.

Delimit Scope algebra_scope with algebra.

Open Scope algebra_scope.

(** TODO Using [\/] with scopes would be smarter. *)

Reserved Notation "x '\_/' y" (at level 50, left associativity).
Reserved Notation "x '/^\' y" (at level 40, left associativity).
Reserved Notation "'_|_'" (at level 0, no associativity).
Reserved Notation "'^|^'" (at level 0, no associativity).

Notation "x '\_/' y" := (join x y) : algebra_scope.
Notation "x '/^\' y" := (meet x y) : algebra_scope.
Notation "'_|_'" := bot : algebra_scope.
Notation "'^|^'" := top : algebra_scope.
