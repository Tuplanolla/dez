From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.Is Require Export
  Equivalence LeftExternallyUnital.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLUn {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A) : Prop := {
  eq_rel_is_eq :> IsEq eq_rel;
  l_un : forall x : A, 0 + x == x;
}.

Section Context.

Context {A : Type} `{is_l_un : IsLUn A}.

Global Instance l_ext_bin_op_un_is_l_ext_un : IsLExtUn l_ext_bin_op un := {}.
Proof. apply l_un. Qed.

End Context.
