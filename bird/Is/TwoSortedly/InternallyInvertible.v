From Maniunfold.Has Require Export
  BinaryRelation Torsion Unit UnaryOperation.
From Maniunfold.Is Require Export
  LeftInternallyInvertible RightInternallyInvertible.

Class IsIntInv {A B : Type} {has_bin_rel : HasBinRel B}
  (has_tor : HasTor A B) (has_un : HasUn B)
  (has_un_op : HasUnOp A) : Prop := {
  tor_un_un_op_is_l_int_inv :> IsLIntInv tor un un_op;
  tor_un_un_op_is_r_int_inv :> IsRIntInv tor un un_op;
}.
