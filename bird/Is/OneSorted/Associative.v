From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.
From Maniunfold.Is Require Export
  ThreeSorted.Bicompatible.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

Class IsAssoc {A : Type} (A_has_bin_op : HasBinOp A) : Prop :=
  assoc : forall x y z : A, x + (y + z) = (x + y) + z.

Section Context.

Context {A : Type} `{is_assoc : IsAssoc A}.

Global Instance bin_op_bin_op_is_bicompat : IsBicompat bin_op bin_op.
Proof. intros x y z. apply assoc. Qed.

End Context.
