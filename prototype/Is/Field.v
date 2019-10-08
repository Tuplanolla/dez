From Maniunfold.Has Require Import EquivalenceRelation
  FieldOperations FieldIdentities FieldInverses.
From Maniunfold.Is Require Import Setoid Ring Inverse.

Class IsField (A : Type) {has_eqv : HasEqv A}
  {has_add : HasAdd A} {has_zero : HasZero A} {has_neg : HasNeg A}
  {has_mul : HasMul A} {has_one : HasOne A} {has_recip : HasRecip A} :
  Prop := {
  add_mul_is_ring :> IsRing A;
  add_is_inverse :> IsInverse A
    (has_opr := has_mul) (has_idn := has_one) (has_inv := has_recip);
}.
