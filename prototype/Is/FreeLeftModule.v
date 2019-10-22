From Coq Require Import
  List.
From Maniunfold.Has Require Export
  Basis Enum.
From Maniunfold.Is Require Export
  Proper FinitelyEnumerable LeftModule.
From Maniunfold.ShouldHave Require Import
  FieldNotations ModuleNotations.

(** TODO Investigate whether the use of
    a nonconstructive existential quantifier is dubious. *)

Class IsFreeLeftModule {A S I : Type} {A_has_eqv : HasEqv A}
  (A_has_opr : HasOpr A) (A_has_idn : HasIdn A) (A_has_inv : HasInv A)
  {S_has_eqv : HasEqv S} (S_has_add : HasAdd S) (S_has_zero : HasZero S)
  (S_has_neg : HasNeg S) (S_has_mul : HasMul S) (S_has_one : HasOne S)
  (has_lsmul : HasLSMul S A)
  {I_has_eqv : HasEqv I} {I_has_enum : HasEnum I}
  (has_basis : HasBasis I A) : Prop := {
  basis_is_proper :> IsProper (eqv ==> eqv) basis;
  I_is_finite :> IsFinite I;
  opr_idn_inv_add_zero_neg_mul_one_lsmul_is_left_module :>
    IsLeftModule opr idn inv add zero neg mul one lsmul;
  spanning : forall x : A, exists coeffs : I -> S,
    let terms (i : I) := coeffs i <* basis i in
    fold_right opr idn (map terms enum) == x;
  independent : forall coeffs : I -> S,
    let terms (i : I) := coeffs i <* basis i in
    fold_right opr idn (map terms enum) == idn ->
    Forall (fun a : S => a == 0) (map coeffs enum);
}.
