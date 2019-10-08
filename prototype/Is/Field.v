From Maniunfold.Has Require Import EquivalenceRelation
  FieldOperations FieldIdentities FieldInverses.
From Maniunfold.Is Require Import Setoid Ring LeftInverse RightInverse.

Class IsField (A : Type) {has_eqv : HasEqv A}
  {has_add : HasAdd A} {has_zero : HasZero A} {has_neg : HasNeg A}
  {has_mul : HasMul A} {has_one : HasOne A} {has_recip : HasRecip A} :
  Prop := {
  add_mul_is_ring :> IsRing A;
  add_is_left_inverse :> IsLeftInverse A
    (has_opr := has_mul) (has_idn := has_one) (has_inv := has_recip);
  add_is_right_inverse :> IsRightInverse A
    (has_opr := has_mul) (has_idn := has_one) (has_inv := has_recip);
}.
