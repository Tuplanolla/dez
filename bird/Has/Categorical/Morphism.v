From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.

Class HasHom (A : Type) : Type := hom : A -> A -> Prop.

Typeclasses Transparent HasHom.

Section Context.

Context {A : Type} `{has_hom : HasHom A}.

Global Instance A_has_bin_rel : HasBinRel A := hom.

End Context.
