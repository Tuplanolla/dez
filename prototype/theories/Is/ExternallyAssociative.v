From Maniunfold.Has Require Export
  EquivalenceRelation ExternalBinaryOperation.
From Maniunfold.Is Require Export
  Setoid.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsExternallyAssociative {A B C : Type} {has_eq_rel : HasEqRel B}
  (has_ex_bi_op_left : HasExBiOp A B)
  (has_ex_bi_op_right : HasExBiOp C B) : Prop := {
  eq_rel_is_setoid :> IsSetoid eq_rel;
  externally_associative : forall (a : A) (x : B) (b : C),
    a <+ (x +> b) == (a <+ x) +> b;
}.
