From DEZ.Has Require Export
  Basis Enum.
From DEZ.Is Require Export
  FreeLeftModule.

(** TODO What is this supposed to be? *)

Class IsGradedFreeLeftModule {G I S A : Type}
  {I_has_eqv : HasEqv I} {I_has_enum : HasEnum I} {S_has_eqv : HasEqv S}
  (S_has_add : HasAdd S) (S_has_zero : HasZero S) (S_has_neg : HasNeg S)
  (S_has_mul : HasMul S) (S_has_one : HasOne S) {A_has_eqv : HasEqv A}
  (A_has_opr : HasOpr A) (A_has_idn : HasIdn A) (A_has_inv : HasInv A)
  (has_lsmul : HasLSMul S A) (has_basis : HasBasis I A) : Prop := {
  opr_idn_inv_add_zero_neg_mul_one_lsmul_basis_is_free_left_module :>
    forall g : G, IsFreeLeftModule opr idn inv add zero neg mul one lsmul basis;
}.
