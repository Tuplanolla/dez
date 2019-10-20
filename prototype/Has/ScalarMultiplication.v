From Maniunfold.Has Require Export
  ScalarOperations.

Delimit Scope module_scope with module.

Open Scope module_scope.

Class HasLSMul (S A : Type) : Type := lsmul : S -> A -> A.
Class HasRSMul (S A : Type) : Type := rsmul : S -> A -> A.

Typeclasses Transparent HasLSMul HasRSMul.

(** TODO Semiring-like structure for the notations. *)

Reserved Notation "a '<*' x" (at level 40, left associativity).
Notation "a '<*' x" := (lsmul a x) : module_scope.

Reserved Notation "x '*>' a" (at level 40, left associativity).
Notation "x '*>' a" := (rsmul a x) : module_scope.

Global Instance lsmul_has_lopr {S A : Type}
  {has_lsmul : HasLSMul S A} : HasLOpr S A := lsmul.
Global Instance rsmul_has_ropr {S A : Type}
  {has_rsmul : HasRSMul S A} : HasROpr S A := rsmul.
