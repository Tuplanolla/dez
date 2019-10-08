From Maniunfold.Has Require Import EquivalenceRelation Operation Identity.
From Maniunfold.Is Require Import Semigroup LeftIdentity RightIdentity.

Class IsMonoid (A : Type)
  {has_eqv : HasEqv A} {has_opr : HasOpr A} {has_idn : HasIdn A} : Prop := {
  opr_is_semigroup :> IsSemigroup A;
  opr_is_left_identity :> IsLeftIdentity A;
  opr_is_right_identity :> IsRightIdentity A;
}.
