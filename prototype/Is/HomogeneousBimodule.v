From Maniunfold.Has Require Export
  ScalarMultiplication.
From Maniunfold.Is Require Export
  Bimodule.

Class IsHomogeneousBimodule (S A : Type) {S_has_eqv : HasEqv S}
  {S_has_add : HasAdd S} {S_has_zero : HasZero S} {S_has_neg : HasNeg S}
  {S_has_mul : HasMul S} {S_has_one : HasOne S}
  {A_has_eqv : HasEqv A}
  {A_has_opr : HasOpr A} {A_has_idn : HasIdn A} {A_has_inv : HasInv A}
  {has_lsmul : HasLSMul S A} {has_rsmul : HasRSMul S A} : Prop := {
  homogeneous_bimodule_is_bimodule :> IsBimodule S S A;
}.
