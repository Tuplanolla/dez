From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation.
From Maniunfold.Is Require Export
  Equivalence Proper.

Class IsMag {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) : Prop := {
  eq_rel_is_eq :> IsEq eq_rel;
  bin_op_is_proper :> IsProper (eq_rel ==> eq_rel ==> eq_rel) bin_op;
}.
