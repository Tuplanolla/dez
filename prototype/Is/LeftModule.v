From Maniunfold.Has Require Export
  ScalarMultiplication.
From Maniunfold.Is Require Export
  Proper Ring AbelianGroup.

Import AdditiveNotations.

Class IsLeftModule {S A : Type} {S_has_eqv : HasEqv S}
  (S_has_add : HasAdd S) (S_has_zero : HasZero S) (S_has_neg : HasNeg S)
  (S_has_mul : HasMul S) (S_has_one : HasOne S) {A_has_eqv : HasEqv A}
  (A_has_opr : HasOpr A) (A_has_idn : HasIdn A) (A_has_inv : HasInv A)
  (has_lsmul : HasLSMul S A) : Prop := {
  left_module_lsmul_is_proper :> IsProper (eqv ==> eqv ==> eqv) lsmul;
  left_module_add_zero_neg_mul_one_is_ring :> IsRing add zero neg mul one;
  left_module_opr_idn_inv_is_abelian_group :> IsAbelianGroup opr idn inv;
  left_module_left_biidentity : forall x : A, 1 <* x == x;
  left_module_left_bicompatible : forall (a b : S) (x : A),
    (a * b) <* x == a <* (b <* x);
  left_module_left_bidistributive : forall (a b : S) (x : A),
    (a + b) <* x == a <* x + b <* x;
  left_module_right_bidistributive : forall (a : S) (x y : A),
    a <* (x + y) == a <* x + a <* y;
}.
