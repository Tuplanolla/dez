From Maniunfold Require Export
  Init.

(** TODO Set the scope. *)

Delimit Scope group_scope with group.

Open Scope group_scope.

Class HasLOpr (S A : Type) : Type := lopr : S -> A -> A.
Class HasROpr (S A : Type) : Type := ropr : S -> A -> A.

Typeclasses Transparent HasLOpr HasROpr.

(** TODO Deprecate notation modules. *)

Module AdditiveNotations.

Reserved Notation "a '<+' x" (at level 50, left associativity).
Notation "a '<+' x" := (lopr a x) : group_scope.
Reserved Notation "x '+>' a" (at level 50, left associativity).
Notation "x '+>' a" := (ropr a x) : group_scope.

End AdditiveNotations.

Module MultiplicativeNotations.

Reserved Notation "a '<*' x" (at level 40, left associativity).
Notation "a '<*' x" := (lopr a x) : group_scope.
Reserved Notation "x '*>' a" (at level 40, left associativity).
Notation "x '*>' a" := (ropr a x) : group_scope.

End MultiplicativeNotations.
