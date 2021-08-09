From DEZ.Has Require Export
  GroupOperation.

Class HasPow (A : Type) : Type := pow : A -> A -> A.

Typeclasses Transparent HasPow.

Global Instance pow_has_opr {A : Type} {has_pow : HasPow A} : HasOpr A := pow.
