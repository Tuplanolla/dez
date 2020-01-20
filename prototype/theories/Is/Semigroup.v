From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.Is Require Export
  Proper Equivalence Associative.

Class IsSGrp {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) : Prop := {
  bin_op_is_proper :> IsProper (eq_rel ==> eq_rel ==> eq_rel) bin_op;
  bin_op_is_associative :> IsAssoc bin_op;
}.
