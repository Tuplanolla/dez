From Maniunfold.Has Require Export
  LeftTorsion.

Class HasBinRel (A : Type) : Type := bin_rel : A -> A -> Prop.

Typeclasses Transparent HasBinRel.

Section Context.

Context {A : Type} `{has_bin_rel : HasBinRel A}.

Global Instance A_Prop_has_l_tor : HasLTor A Prop := bin_rel.

End Context.
