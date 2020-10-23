From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.

(** Apartness relation, constructive inequality. *)

Class HasApartRel (A : Type) : Type := apart_rel : A -> A -> Prop.

Typeclasses Transparent HasApartRel.

Section Context.

Context {A : Type} `{HasApartRel A}.

Global Instance A_has_bin_rel : HasBinRel A := apart_rel.

End Context.
