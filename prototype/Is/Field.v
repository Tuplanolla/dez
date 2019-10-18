From Maniunfold.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities FieldInverses.
From Maniunfold.Is Require Export
  Proper Ring Invertible.

(** TODO Remember division by zero. *)

Class IsField {A : Type} {has_eqv : HasEqv A}
  (has_add : HasAdd A) (has_zero : HasZero A) (has_neg : HasNeg A)
  (has_mul : HasMul A) (has_one : HasOne A) (has_recip : HasRecip A) :
  Prop := {
  field_recip_is_proper :> IsProper (eqv ==> eqv) recip;
  field_is_ring :> IsRing add zero neg mul one;
  field_mul_is_invertible :> IsInvertible mul one recip;
}.
