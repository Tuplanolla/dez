From Maniunfold.Has Require Import EquivalenceRelation
  FieldOperations FieldIdentities FieldInverses.
From Maniunfold.Is Require Import Setoid Semiring LeftInverse RightInverse.

Class IsRing (A : Type) {has_eqv : HasEqv A}
  {has_add : HasAdd A} {has_zero : HasZero A} {has_neg : HasNeg A}
  {has_mul : HasMul A} {has_one : HasOne A} : Prop := {
  add_mul_is_semiring :> IsSemiring A;
  add_is_left_inverse :> IsLeftInverse A
    (has_opr := has_add) (has_idn := has_zero) (has_inv := has_neg);
  add_is_right_inverse :> IsRightInverse A
    (has_opr := has_add) (has_idn := has_zero) (has_inv := has_neg);
}.
