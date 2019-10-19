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
  lsmul_is_proper :> IsProper (eqv ==> eqv ==> eqv) lsmul;
  add_zero_neg_mul_one_is_ring :> IsRing add zero neg mul one;
  opr_idn_inv_is_abelian_group :> IsAbelianGroup opr idn inv;
  left_biidentifiable : forall x : A, 1 <* x == x;
  left_bicompatible : forall (a b : S) (x : A),
    (a * b) <* x == a <* (b <* x);
  left_bidistributive : forall (a b : S) (x : A),
    (a + b) <* x == a <* x + b <* x;
  right_bidistributive : forall (a : S) (x y : A),
    a <* (x + y) == a <* x + a <* y;
}.
