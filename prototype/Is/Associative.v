From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation.
From Maniunfold.Is Require Export
  Setoid.

Import AdditiveNotations.

Class IsAssociative {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) : Prop := {
  associative_is_setoid :> IsSetoid A;
  associative : forall x y z : A, x + (y + z) == (x + y) + z;
}.
