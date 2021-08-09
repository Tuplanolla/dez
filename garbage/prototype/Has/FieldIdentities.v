From DEZ.Has Require Export
  GroupOperation GroupIdentity FieldOperations.

Class HasZero (A : Type) : Type := zero : A.
Class HasOne (A : Type) : Type := one : A.

Typeclasses Transparent HasZero HasOne.

Section Context.

Context {A : Type} {has_zero : HasZero A}.

Global Instance zero_has_idn : HasIdn A := zero.

End Context.

Section Context.

Context {A : Type} {has_one : HasOne A}.

Global Instance one_has_idn : HasIdn A := one.

End Context.
