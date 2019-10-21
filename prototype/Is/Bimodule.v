From Maniunfold.Has Require Export
  ScalarMultiplication.
From Maniunfold.Is Require Export
  LeftModule RightModule Heteroassociative.

Class IsBimodule {A LS RS : Type} {A_has_eqv : HasEqv A}
  (A_has_opr : HasOpr A) (A_has_idn : HasIdn A) (A_has_inv : HasInv A)
  {LS_has_eqv : HasEqv LS}
  (LS_has_add : HasAdd LS) (LS_has_zero : HasZero LS) (LS_has_neg : HasNeg LS)
  (LS_has_mul : HasMul LS) (LS_has_one : HasOne LS)
  {RS_has_eqv : HasEqv RS}
  (RS_has_add : HasAdd RS) (RS_has_zero : HasZero RS) (RS_has_neg : HasNeg RS)
  (RS_has_mul : HasMul RS) (RS_has_one : HasOne RS)
  (has_lsmul : HasLSMul LS A) (has_rsmul : HasRSMul RS A) : Prop := {
  opr_idn_inv_add_zero_neg_mul_one_lsmul_is_left_module :>
    IsLeftModule opr idn inv add zero neg mul one lsmul;
  opr_idn_inv_add_zero_neg_mul_one_rsmul_is_right_module :>
    IsRightModule opr idn inv add zero neg mul one rsmul;
  lsmul_rsmul_is_heteroassociative : IsHeteroassociative lsmul rsmul;
}.
