From Maniunfold.Has Require Export
  BinaryRelation BinaryOperation UnaryOperation.
From Maniunfold.ShouldHave Require Import
  BinaryRelationNotations AdditiveNotations.

Class IsExtAntidistr {A : Type} {has_bin_rel : HasBinRel A}
  (has_bin_op : HasBinOp A) (has_un_op : HasUnOp A) : Prop :=
  ext_antidistr : forall x y : A, >-< (x >+< y) ~~ >-< y >+< >-< x.
