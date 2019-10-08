From Maniunfold.Has Require Import EquivalenceRelation
  GroupOperation GroupIdentity GroupInverse.
From Maniunfold.Is Require Import Setoid.

Import AdditiveNotations.

Class IsLeftInverse (A : Type) {has_eqv : HasEqv A}
  {has_opr : HasOpr A} {has_idn : HasIdn A} {has_inv : HasInv A} : Prop := {
  eqv_is_setoid :> IsSetoid A;
  opr_left_inverse : forall x : A, (- x) + x == 0;
}.
