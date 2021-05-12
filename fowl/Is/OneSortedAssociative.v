From Maniunfold.Has Require Export
  OneSortedBinaryOperation.
From Maniunfold.Is Require Export
  ThreeSortedBicompatible.
From Maniunfold.ShouldHave Require Import
  OneSortedAdditiveNotations.

(** Associative binary operation. *)

Class IsAssoc (A : Type) `(HasBinOp A) : Prop :=
  assoc : forall x y z : A, x + (y + z) = (x + y) + z.

Section Context.

Context (A : Type) `{IsAssoc A}.

Global Instance A_A_A_bin_op_bin_op_is_bicompat :
  IsBicompat (bin_op (A := A)) (bin_op (A := A)).
Proof. intros x y z. apply assoc. Defined.

End Context.
