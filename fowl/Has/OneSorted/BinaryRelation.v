From Maniunfold.Has Require Export
  TwoSorted.BinaryRelation.

(** Binary relation. *)

Class HasBinRel (A : Type) : Type := bin_rel : A -> A -> Prop.

Typeclasses Transparent HasBinRel.

Section Context.

Context {A : Type} `{HasBinRel A}.

Global Instance A_A_has_two_bin_rel : HasTwoBinRel A A := bin_rel.

End Context.
