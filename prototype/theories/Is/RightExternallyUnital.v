From Maniunfold.Has Require Export
  EquivalenceRelation RightExternalBinaryOperation.
From Maniunfold.Is Require Export
  Equivalence.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsRExtUn {A B : Type} {has_eq_rel : HasEqRel B}
  (has_r_ext_bin_op : HasRExtBinOp A B) (has_un : HasUn A) : Prop := {
  eq_rel_is_eq :> IsEq eq_rel;
  r_ext_un : forall x : B, x >+ 0 == x;
}.
