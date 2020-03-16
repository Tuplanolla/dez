From Coq Require Import
  ZArith.
From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation UnaryOperation LeftAction.
From Maniunfold.Offers Require Import
  PositivePowers.
From Maniunfold.ShouldHave Require Import
  AdditiveNotations.

Section Context.

Context {A : Type} `{has_bin_op : HasBinOp A} `{has_null_op : HasNullOp A}
  `{has_un_op : HasUnOp A}.

Definition z_op (n : Z) (x : A) : A :=
  match n with
  | Z0 => 0
  | Zpos p => positive_op p x
  | Zneg p => - positive_op p x
  end.

Global Instance Z_A_has_l_act : HasLAct Z A := z_op.

End Context.
