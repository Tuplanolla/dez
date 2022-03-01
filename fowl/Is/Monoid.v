(** * Monoidal Structure *)

From DEZ.Has Require Export
  AlgebraicForms AlgebraicOperations EquivalenceRelations.
From DEZ.Is Require Export
  Semigroup Unital.

(** ** Monoid *)

Class IsMon (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A) : Prop := {
  is_semigrp :> IsSemigrp X k;
  is_unl_l_r :> IsUnlLR X x k;
}.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (k : A -> A -> A)
  `{!IsMon X x k}.

#[local] Instance has_equiv_rel : HasEquivRel A := X.
#[local] Instance has_null_op : HasNullOp A := x.
#[local] Instance has_bin_op : HasBinOp A := k.

Ltac note := progress (
  try change X with (equiv_rel (A := A)) in *;
  try change x with (null_op (A := A)) in *;
  try change k with (bin_op (A := A)) in *).

#[local] Instance is_proper : IsProper X x.
Proof. unfold IsProper. reflexivity. Qed.

End Context.
