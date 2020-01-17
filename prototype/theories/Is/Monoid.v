From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit.
From Maniunfold.Is Require Export
  Semigroup Unital.

Class IsMonoid {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A) : Prop := {
  bin_op_is_semigroup :> IsSemigroup bin_op;
  bin_op_un_is_unital :> IsUnital bin_op un;
}.
