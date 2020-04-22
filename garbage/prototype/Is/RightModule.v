From Maniunfold.Has Require Export
  ScalarMultiplication.
From Maniunfold.Is Require Export
  Proper Ring AbelianGroup.
From Maniunfold.ShouldHave Require Import
  FieldNotations AdditiveGroupNotations ModuleNotations.

Class IsRightModule {A S : Type} {A_has_eqv : HasEqv A}
  (A_has_opr : HasOpr A) (A_has_idn : HasIdn A) (A_has_inv : HasInv A)
  {S_has_eqv : HasEqv S}
  (S_has_add : HasAdd S) (S_has_zero : HasZero S) (S_has_neg : HasNeg S)
  (S_has_mul : HasMul S) (S_has_one : HasOne S)
  (has_rsmul : HasRSMul S A) : Prop := {
  rsmul_is_proper :> IsProper (eqv ==> eqv ==> eqv) rsmul;
  add_zero_neg_mul_one_is_ring :> IsRing add zero neg mul one;
  opr_idn_inv_is_abelian_group :> IsAbelianGroup (A := A) opr idn inv;
  right_biidentity : forall x : A, x *> 1 == x;
  right_bicompatible : forall (a b : S) (x : A),
    x *> (a * b) == (x *> a) *> b;
  left_bidistributive : forall (a b : S) (x : A),
    x *> (a + b) == x *> a + x *> b;
  right_bidistributive : forall (a : S) (x y : A),
    (x + y) *> a == x *> a + y *> a;
}.
