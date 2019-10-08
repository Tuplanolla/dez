From Maniunfold.Has Require Import EquivalenceRelation
  GroupOperation GroupIdentity GroupInverse.
From Maniunfold.Is Require Export LeftInverse RightInverse.

Import AdditiveNotations.

Class IsInverse (A : Type) {has_eqv : HasEqv A}
  {has_opr : HasOpr A} {has_idn : HasIdn A} {has_inv : HasInv A} : Prop := {
  opr_is_left_inverse :> IsLeftInverse A;
  opr_is_right_inverse :> IsRightInverse A;
}.
