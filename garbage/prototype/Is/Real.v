From DEZ.Has Require Export
  EquivalenceRelation FieldOperations FieldIdentities FieldInverses.
From DEZ.Is Require Export
  TotalOrder Field.
From DEZ.ShouldHave Require Import
  OrderNotations FieldNotations.

(** TODO This is probably wrong in many ways,
    as the existential quantifier might have to be constructive.
    Still, this provides a rough idea of
    how the existence of real numbers can be postulated. *)

Class IsReal {A : Type} {has_eqv : HasEqv A} {has_ord : HasOrd A}
  (has_add : HasAdd A) (has_zero : HasZero A) (has_neg : HasNeg A)
  (has_mul : HasMul A) (has_one : HasOne A) (has_recip : HasRecip A) :
  Prop := {
  ord_is_total_order :> IsTotalOrder ord;
  add_zero_neg_mul_one_recip_is_field :>
    IsField add zero neg mul one recip;
  left_monotone : forall x y z : A, x <= y -> z + x <= z + y;
  monotone : forall x y : A, 0 <= x -> 0 <= y -> 0 <= x * y;
  complete : forall P Q : A -> Prop,
    (forall x y : A, P x -> Q y -> x < y) ->
    exists z : A, forall x y : A, P x -> Q y ->
    x =/= z -> y =/= z -> x < z /\ z < y;
}.
