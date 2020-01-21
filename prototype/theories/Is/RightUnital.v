From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.Is Require Export
  Equivalence RightExternallyUnital.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsRUn {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A) : Prop :=
  r_un : forall x : A, x + 0 == x.

Section Context.

Context {A : Type} `{is_r_un : IsRUn A}.

Global Instance r_ext_bin_op_un_is_r_ext_un : IsRExtUn r_ext_bin_op un.
Proof. intros x. apply r_un. Qed.

End Context.
