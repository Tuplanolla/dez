From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit.
From Maniunfold.Is Require Export
  Semigroup Unital.

Class IsMonoid {A : Type} {has_eq_rel : HasEqRel A}
  (has_bi_op : HasBiOp A) (has_un : HasUn A) : Prop := {
  bi_op_is_semigroup :> IsSemigroup bi_op;
  bi_op_un_is_unital :> IsUnital bi_op un;
}.
