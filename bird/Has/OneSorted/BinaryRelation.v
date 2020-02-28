From Maniunfold.Has Require Export
  TwoSorted.BinaryRelation.

Class HasBinRel (A : Type) : Type := bin_rel : A -> A -> Prop.

Typeclasses Transparent HasBinRel.

Section Context.

Context {A : Type} `{has_bin_rel : HasBinRel A}.

Global Instance A_has_bin_rel_2 : HasBinRel2 A A := bin_rel.

End Context.
