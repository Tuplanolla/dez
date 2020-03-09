From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation LeftAction.
From Maniunfold.Is Require Export
  Equivalence Magma Proper.

Class IsLMagAct {A B : Type}
  {A_has_eq_rel : HasEqRel A} {B_has_eq_rel : HasEqRel B}
  (A_has_bin_op : HasBinOp A) (has_l_act : HasLAct A B) : Prop := {
  eq_rel_is_eq :> IsEq (A := B) eq_rel;
  bin_op_is_mag :> IsMag (A := A) bin_op;
  l_act_is_proper :> IsProper (eq_rel ==> eq_rel ==> eq_rel) l_act;
}.
