From Maniunfold.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities FieldInverses.
From Maniunfold.Is Require Export
  Ring Invertible.

(** TODO Remember division by zero. *)

Class IsField {A : Type} {has_eqv : HasEqv A}
  (has_add : HasAdd A) (has_zero : HasZero A) (has_neg : HasNeg A)
  (has_mul : HasMul A) (has_one : HasOne A) (has_recip : HasRecip A) :
  Prop := {
  field_recip_is_proper :> IsProper (eqv ==> eqv) recip;
  field_is_ring :> IsRing add zero neg mul one;
  field_mul_is_invertible :> IsInvertible mul one recip;
}.

Add Parametric Morphism {A : Type} `{is_field : IsField A} : recip
  with signature eqv ==> eqv
  as eqv_recip_morphism.
Proof. apply field_recip_is_proper; auto. Qed.
