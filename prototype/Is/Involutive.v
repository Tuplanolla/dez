From Maniunfold.Has Require Import EquivalenceRelation
  GroupOperation GroupInverse.
From Maniunfold.Is Require Import Setoid.

Import AdditiveNotations.

Class IsInvolutive (A : Type)
  {has_eqv : HasEqv A} {has_inv : HasInv A} : Prop := {
  eqv_is_setoid :> IsSetoid A;
  inv_involutive : forall x : A, - (- x) == x;
}.
