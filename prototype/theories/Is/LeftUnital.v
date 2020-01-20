From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.Is Require Export
  Equivalence LeftExternallyUnital.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLUn {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A) : Prop := {
  eq_rel_is_setoid :> IsEq eq_rel;
  left_unital : forall x : A, 0 + x == x;
}.

Section Context.

Context {A : Type} `{is_left_unital : IsLUn A}.

Global Instance left_unital_is_left_external_unital :
  IsLExtUn l_ext_bin_op un := {}.
Proof. intros x. apply left_unital. Qed.

End Context.
