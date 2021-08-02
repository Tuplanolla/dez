From Coq Require Import
  ZArith.ZArith.
From Maniunfold.Has Require Export
  Action.
From Maniunfold.Is Require Export
  Group.
From Maniunfold.Offers Require Export
  OneSortedPositiveOperations OneSortedNaturalOperations.
From Maniunfold.ShouldOffer Require Import
  OneSortedAdditivePositiveOperationNotations.

Section Context.

Context (A : Type) (Hk : HasBinOp A) (Hx : HasNullOp A) (Hf : HasUnOp A)
  `(IsGrp A).
(* Context (A : Type) (Hx : HasNullOp A) (Hf : HasUnOp A) (Hk : HasBinOp A)
  `(IsGrp A). *)

Definition z_op (n : Z) (x : A) : A :=
  match n with
  | Z0 => 0
  | Zpos p => (p * x)%positive
  | Zneg p => - (p * x)%positive
  end.

Global Instance Z_A_has_act_l : HasActL Z A := z_op.

End Context.

Arguments z_op {_} _ _ _ !_ _.
