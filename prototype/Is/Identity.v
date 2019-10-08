From Maniunfold.Has Require Import EquivalenceRelation
  GroupOperation GroupIdentity.
From Maniunfold.Is Require Export LeftIdentity RightIdentity.

Import AdditiveNotations.

Class IsIdentity (A : Type)
  {has_eqv : HasEqv A} {has_opr : HasOpr A} {has_idn : HasIdn A} : Prop := {
  opr_is_left_identity :> IsLeftIdentity A;
  opr_is_right_identity :> IsRightIdentity A;
}.
