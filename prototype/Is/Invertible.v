From Maniunfold.Has Require Import EquivalenceRelation
  GroupOperation GroupIdentity GroupInverse.
From Maniunfold.Is Require Export LeftInvertible RightInvertible.

Import AdditiveNotations.

Class IsInvertible (A : Type) {has_eqv : HasEqv A}
  {has_opr : HasOpr A} {has_idn : HasIdn A} {has_inv : HasInv A} : Prop := {
  opr_is_left_invertible :> IsLeftInvertible A;
  opr_is_right_invertible :> IsRightInvertible A;
}.
