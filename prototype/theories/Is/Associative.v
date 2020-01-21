From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.Is Require Export
  Equivalence ExternallyAssociative.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsAssoc {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) : Prop := {
  eq_rel_is_eq :> IsEq eq_rel;
  assoc : forall x y z : A, x + (y + z) == (x + y) + z;
}.

Section Context.

Context {A : Type} `{is_assoc : IsAssoc A}.

Global Instance bin_op_is_ext_assoc : IsExtAssoc bin_op bin_op.
Proof. constructor; try typeclasses eauto. intros x y z. apply assoc. Qed.

End Context.
