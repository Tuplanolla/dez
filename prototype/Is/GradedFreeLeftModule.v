From Maniunfold.Has Require Export
  Basis Enum.
From Maniunfold.Is Require Export
  FreeLeftModule.

(** TODO What is this supposed to be? *)

Class IsGradedFreeLeftModule (G N S A : Type)
  {N_has_eqv : HasEqv N} {N_has_enum : HasEnum N}
  {S_has_eqv : HasEqv S}
  {S_has_add : HasAdd S} {S_has_zero : HasZero S} {S_has_neg : HasNeg S}
  {S_has_mul : HasMul S} {S_has_one : HasOne S}
  {A_has_eqv : HasEqv A}
  {A_has_opr : HasOpr A} {A_has_idn : HasIdn A} {A_has_inv : HasInv A}
  {has_lsmul : HasLSMul S A}
  {has_basis : HasBasis N A} : Prop := {
  basis_is_free_left_module :> forall g : G, IsFreeLeftModule N S A;
}.
