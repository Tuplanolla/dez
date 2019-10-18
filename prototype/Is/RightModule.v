From Maniunfold.Has Require Export
  ScalarMultiplication.
From Maniunfold.Is Require Export
  Proper Ring AbelianGroup.

Import AdditiveNotations.

Class IsRightModule {S A : Type} {S_has_eqv : HasEqv S}
  (S_has_add : HasAdd S) (S_has_zero : HasZero S) (S_has_neg : HasNeg S)
  (S_has_mul : HasMul S) (S_has_one : HasOne S) {A_has_eqv : HasEqv A}
  (A_has_opr : HasOpr A) (A_has_idn : HasIdn A) (A_has_inv : HasInv A)
  (has_rsmul : HasRSMul S A) : Prop := {
  right_module_rsmul_is_proper :> IsProper (eqv ==> eqv ==> eqv) rsmul;
  right_module_add_zero_neg_mul_one_is_ring :> IsRing add zero neg mul one;
  right_module_opr_idn_inv_is_abelian_group :> IsAbelianGroup opr idn inv;
  right_module_right_biidentity : forall x : A, x *> 1 == x;
  right_module_right_bicompatible : forall (a b : S) (x : A),
    x *> (a * b) == (x *> a) *> b;
  right_module_left_bidistributive : forall (a b : S) (x : A),
    x *> (a + b) == x *> a + x *> b;
  right_module_right_bidistributive : forall (a : S) (x y : A),
    (x + y) *> a == x *> a + y *> a;
}.
