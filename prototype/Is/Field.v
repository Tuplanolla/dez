From Maniunfold.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities FieldInverses.
From Maniunfold.Is Require Export
  Proper Ring Biinvertible.

(** TODO Remember division by zero.
    Also handle discrete and residue fields differently. *)

Class IsField {A : Type} {has_eqv : HasEqv A}
  (has_add : HasAdd A) (has_zero : HasZero A) (has_neg : HasNeg A)
  (has_mul : HasMul A) (has_one : HasOne A) (has_recip : HasRecip A) :
  Prop := {
  recip_is_proper :> IsProper (eqv ==> eqv) recip;
  add_zero_neg_mul_one_is_ring :> IsRing add zero neg mul one;
  mul_one_recip_is_invertible :> IsBiinvertible mul one recip;
}.
