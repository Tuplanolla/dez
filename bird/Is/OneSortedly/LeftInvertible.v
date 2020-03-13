From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit UnaryOperation.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLInv {A : Type} (has_bin_op : HasBinOp A)
  (has_un : HasUn A) (has_un_op : HasUnOp A) : Prop :=
  l_inv : forall x : A, - x + x = 0.
