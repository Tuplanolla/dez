From DEZ.Has Require Export
  GroupOperation.

Class HasAdd (A : Type) : Type := add : A -> A -> A.
Class HasMul (A : Type) : Type := mul : A -> A -> A.

Typeclasses Transparent HasAdd HasMul.

Global Instance add_has_opr {A : Type} {has_add : HasAdd A} : HasOpr A := add.
Global Instance mul_has_opr {A : Type} {has_mul : HasMul A} : HasOpr A := mul.
