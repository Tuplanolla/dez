From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation GroupIdentity GroupInverse.
From Maniunfold.Is Require Export
  Setoid.

Import AdditiveNotations.

Class IsRightInvertible {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) (has_idn : HasIdn A) (has_inv : HasInv A) : Prop := {
  right_invertible_eqv_is_setoid :> IsSetoid eqv;
  right_invertible : forall x : A, x + (- x) == 0;
}.
