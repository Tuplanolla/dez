From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.Is Require Export
  Equivalence RightExternallyUnital.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsRUn {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A) : Prop := {
  eq_rel_is_setoid :> IsEq eq_rel;
  right_unital : forall x : A, x + 0 == x;
}.

Section Context.

Context {A : Type} `{is_right_unital : IsRUn A}.

Global Instance right_unital_is_right_external_unital :
  IsRExtUn l_ext_bin_op un := {}.
Proof. intros x. apply right_unital. Qed.

End Context.
