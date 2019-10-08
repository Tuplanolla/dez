From Maniunfold.Has Require Import EquivalenceRelation
  Operation Identity Inverse.
From Maniunfold.Is Require Import Group LeftIdentity RightIdentity.

Class IsAbelianGroup (A : Type) {has_eqv : HasEqv A}
  {has_opr : HasOpr A} {has_idn : HasIdn A} {has_inv : HasInv A} : Prop := {
  opr_is_group :> IsGroup A;
  opr_is_left_identity :> IsLeftIdentity A;
  opr_is_right_identity :> IsRightIdentity A;
}.
