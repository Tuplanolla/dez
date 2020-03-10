From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit UnaryOperation.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsRInv {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A)
  (has_un_op : HasUnOp A) : Prop :=
  r_inv : forall x : A, x + - x == 0.

Class IsRInvE {A : Type} (has_bin_op : HasBinOp A)
  (has_un : HasUn A) (has_un_op : HasUnOp A) : Prop :=
  r_invE : forall x : A, x + - x = 0.
