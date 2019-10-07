From Maniunfold.Has Require Import EquivalenceRelation
  Operation Identity Inverse.
From Maniunfold.Is Require Import Setoid Monoid LeftInverse RightInverse.

Import AdditiveNotations.

Class IsGroup (A : Type) {has_eqv : HasEqv A}
  {has_opr : HasOpr A} {has_idn : HasIdn A} {has_inv : HasInv A} : Prop := {
  inv_proper : inv ::> eqv ==> eqv;
  opr_idn_is_monoid :> IsMonoid A;
  opr_idn_inv_is_left_inverse : IsLeftInverse A;
  opr_idn_inv_is_right_inverse : IsRightInverse A;
}.
