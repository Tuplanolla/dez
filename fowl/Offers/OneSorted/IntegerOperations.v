From Coq Require Import
  ZArith.ZArith.
From Maniunfold.Has Require Export
  TwoSorted.LeftAction.
From Maniunfold.Is Require Export
  OneSorted.Group.
From Maniunfold.Offers Require Export
  OneSorted.PositiveOperations OneSorted.NaturalOperations.
From Maniunfold.ShouldOffer Require Import
  OneSorted.AdditivePositiveOperationNotations.

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
