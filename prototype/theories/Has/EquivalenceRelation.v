From Maniunfold.Has Require Export
  BinaryRelation.

Class HasEqRel (A : Type) : Type := eq_rel : A -> A -> Prop.

Typeclasses Transparent HasEqRel.

Section Context.

Context {A : Type} `{has_eq_rel : HasEqRel A}.

Global Instance eq_rel_has_bi_rel : HasBinRel A := eq_rel.

End Context.
