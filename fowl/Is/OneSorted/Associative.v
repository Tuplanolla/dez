From Maniunfold.Has Require Export
  OneSorted.BinaryOperation.
From Maniunfold.Is Require Export
  ThreeSorted.Bicompatible.
From Maniunfold.ShouldHave Require Import
  OneSorted.AdditiveNotations.

(** Associative binary operation. *)

Class IsAssoc (A : Type) `(HasBinOp A) : Prop :=
  assoc : forall x y z : A, x + (y + z) = (x + y) + z.

Section Context.

Context {A : Type} `{IsAssoc A}.

Global Instance A_A_A_bin_op_bin_op_is_bicompat :
  IsBicompat A A A bin_op bin_op.
Proof. intros x y z. apply assoc. Defined.

End Context.
