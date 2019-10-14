From Maniunfold.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities FieldInverses.
From Maniunfold.Is Require Export
  Ring Invertible.

(** TODO Remember division by zero. *)

Class IsField (A : Type) {has_eqv : HasEqv A}
  {has_add : HasAdd A} {has_zero : HasZero A} {has_neg : HasNeg A}
  {has_mul : HasMul A} {has_one : HasOne A} {has_recip : HasRecip A} :
  Prop := {
  recip_proper : recip ::> eqv ==> eqv;
  add_mul_is_ring :> IsRing A;
  mul_is_invertible :> IsInvertible A
    (has_opr := has_mul) (has_idn := has_one) (has_inv := has_recip);
}.

Add Parametric Morphism {A : Type} `{is_field : IsField A} : recip
  with signature eqv ==> eqv
  as eqv_recip_morphism.
Proof. intros x y p. apply recip_proper; auto. Qed.
