From Maniunfold.Has Require Export
  ScalarMultiplication.
From Maniunfold.Is Require Export
  LeftModule RightModule.

Class IsBimodule (LS RS A : Type) {S_has_eqv : HasEqv LS}
  {LS_has_add : HasAdd LS} {LS_has_zero : HasZero LS} {LS_has_neg : HasNeg LS}
  {LS_has_mul : HasMul LS} {LS_has_one : HasOne LS}
  {RS_has_eqv : HasEqv RS}
  {RS_has_add : HasAdd RS} {RS_has_zero : HasZero RS} {RS_has_neg : HasNeg RS}
  {RS_has_mul : HasMul RS} {RS_has_one : HasOne RS}
  {A_has_eqv : HasEqv A}
  {A_has_opr : HasOpr A} {A_has_idn : HasIdn A} {A_has_inv : HasInv A}
  {has_lsmul : HasLSMul LS A} {has_rsmul : HasRSMul RS A} : Prop := {
  bimodule_is_left_module :> IsLeftModule LS A;
  bimodule_is_right_module :> IsRightModule RS A;
  bimodule_lsmul_rsmul_compatible : forall (a : LS) (b : RS) (x : A),
    (a <* x) *> b == a <* (x *> b);
}.
