From Maniunfold.Has Require Export
  TwoSorted.BinaryRelation.

Class HasBinRel (A : Type) : Type := bin_rel : A -> A -> Prop.

Typeclasses Transparent HasBinRel.

Section Context.

Context {A : Type} `{A_has_bin_rel : HasBinRel A}.

Global Instance A_has_two_bin_rel : HasTwoBinRel A A := bin_rel.

End Context.
