From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.Is Require Export
  Proper Setoid Associative.

Class IsSemigroup {A : Type} {has_eq_rel : HasEqRel A}
  (has_bi_op : HasBinOp A) : Prop := {
  bi_op_is_proper :> IsProper (eq_rel ==> eq_rel ==> eq_rel) bi_op;
  bi_op_is_associative :> IsAssociative bi_op;
}.
