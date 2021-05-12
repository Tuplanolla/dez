From Coq Require Import
  ZArith.ZArith.
From Maniunfold.Has Require Export
  TwoSortedLeftAction.
From Maniunfold.Is Require Export
  OneSortedGroup.
From Maniunfold.Offers Require Export
  OneSortedPositiveOperations OneSortedNaturalOperations.
From Maniunfold.ShouldOffer Require Import
  OneSortedAdditivePositiveOperationNotations.

Section Context.

Context (A : Type) `{IsGrp A}.

Definition z_op (n : Z) (x : A) : A :=
  match n with
  | Z0 => 0
  | Zpos p => (p * x)%positive
  | Zneg p => - (p * x)%positive
  end.

Global Instance Z_A_has_l_act : HasLAct Z A := z_op.

End Context.

Arguments z_op {_} _ _ _ !_ _.
