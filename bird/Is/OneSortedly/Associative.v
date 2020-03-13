From Maniunfold.Has.OneSorted Require Export
  BinaryOperation.
From Maniunfold.Is.ThreeSortedly Require Export
  Bicompatible.
From Maniunfold.ShouldHave.OneSorted Require Import
  AdditiveNotations.

Class IsAssoc {A : Type} (has_bin_op : HasBinOp A) : Prop :=
  assoc : forall x y z : A, x + (y + z) = (x + y) + z.

Section Context.

Context {A : Type} `{is_assoc : IsAssoc A}.

Global Instance bin_op_bin_op_is_bicompatible : IsBicompat bin_op bin_op.
Proof. intros x y z. apply assoc. Qed.

End Context.
