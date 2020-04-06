(* bad *)
From Coq Require Import
  ZArith.
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation TwoSorted.LeftAction.
From Maniunfold.Offers Require Export
  PositivePowers.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Section Context.

Context {A : Type} {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  {A_has_un_op : HasUnOp A}.

Definition z_op (n : Z) (x : A) : A :=
  match n with
  | Z0 => 0
  | Zpos p => positive_op p x
  | Zneg p => - positive_op p x
  end.

Global Instance Z_A_has_l_act : HasLAct Z A := z_op.

End Context.
