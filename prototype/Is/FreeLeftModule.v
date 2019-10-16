From Coq Require Import List.
From Maniunfold.Has Require Export
  Basis Enum.
From Maniunfold.Is Require Export
  FinitelyEnumerable LeftModule.

(** TODO Investigate whether the use of
    a nonconstructive existential quantifier is dubious. *)

Class IsFreeLeftModule (I S A : Type)
  {I_has_eqv : HasEqv I} {I_has_enum : HasEnum I}
  {S_has_eqv : HasEqv S}
  {S_has_add : HasAdd S} {S_has_zero : HasZero S} {S_has_neg : HasNeg S}
  {S_has_mul : HasMul S} {S_has_one : HasOne S}
  {A_has_eqv : HasEqv A}
  {A_has_opr : HasOpr A} {A_has_idn : HasIdn A} {A_has_inv : HasInv A}
  {has_lsmul : HasLSMul S A}
  {has_basis : HasBasis I A} : Prop := {
  I_enum_is_finitely_enumerable :> IsFinitelyEnumerable I;
  A_lsmul_is_left_module :> IsLeftModule S A;
  basis_proper :> IsProper (eqv ==> eqv) basis;
  basis_spanning : forall x : A, exists coeffs : I -> S,
    let terms (i : I) := coeffs i <* basis i in
    fold_right opr idn (map terms enum) == x;
  basis_independent : forall coeffs : I -> S,
    let terms (i : I) := coeffs i <* basis i in
    fold_right opr idn (map terms enum) == idn ->
    Forall (fun a : S => a == 0) (map coeffs enum);
}.

Add Parametric Morphism {I S A : Type}
  `{is_free_left_module : IsFreeLeftModule I S A} : basis
  with signature eqv ==> eqv
  as eqv_basis_morphism.
Proof. intros x y p. apply basis_proper; auto. Qed.
