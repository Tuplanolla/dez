From DEZ.Has Require Export
  ScalarOperations.

Class HasLSMul (S A : Type) : Type := lsmul : S -> A -> A.
Class HasRSMul (S A : Type) : Type := rsmul : S -> A -> A.

Typeclasses Transparent HasLSMul HasRSMul.

Global Instance lsmul_has_lopr {S A : Type}
  {has_lsmul : HasLSMul S A} : HasLOpr S A := lsmul.
Global Instance rsmul_has_ropr {S A : Type}
  {has_rsmul : HasRSMul S A} : HasROpr S A := rsmul.
