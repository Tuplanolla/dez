From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.Is Require Export
  Setoid LeftExternallyUnital.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsLeftUnital {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A) : Prop := {
  eq_rel_is_setoid :> IsSetoid eq_rel;
  left_unital : forall x : A, 0 + x == x;
}.

Section Context.

Context {A : Type} `{is_left_unital : IsLeftUnital A}.

Global Instance left_unital_is_left_external_unital :
  IsLeftExternallyUnital l_ex_bin_op un := {}.
Proof. intros x. apply left_unital. Qed.

End Context.
