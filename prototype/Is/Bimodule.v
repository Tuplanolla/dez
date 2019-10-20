From Maniunfold.Has Require Export
  ScalarMultiplication.
From Maniunfold.Is Require Export
  LeftModule RightModule Heteroassociative.

Class IsBimodule {LS RS A : Type} {LS_has_eqv : HasEqv LS}
  (LS_has_add : HasAdd LS) (LS_has_zero : HasZero LS) (LS_has_neg : HasNeg LS)
  (LS_has_mul : HasMul LS) (LS_has_one : HasOne LS) {RS_has_eqv : HasEqv RS}
  (RS_has_add : HasAdd RS) (RS_has_zero : HasZero RS) (RS_has_neg : HasNeg RS)
  (RS_has_mul : HasMul RS) (RS_has_one : HasOne RS) {A_has_eqv : HasEqv A}
  (A_has_opr : HasOpr A) (A_has_idn : HasIdn A) (A_has_inv : HasInv A)
  (has_lsmul : HasLSMul LS A) (has_rsmul : HasRSMul RS A) : Prop := {
  add_zero_neg_mul_one_opr_idn_inv_lsmul_is_left_module :>
    IsLeftModule add zero neg mul one opr idn inv lsmul;
  add_zero_neg_mul_one_opr_idn_inv_rsmul_is_right_module :>
    IsRightModule add zero neg mul one opr idn inv rsmul;
  lsmul_rsmul_is_heteroassociative : IsHeteroassociative lsmul rsmul;
}.
