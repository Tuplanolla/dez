From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.

(** Equivalence relation, equality, similarity. *)

Class HasEqRel (A : Type) : Type := eq_rel : A -> A -> Prop.

Typeclasses Transparent HasEqRel.

Section Context.

Context (A : Type) `(HasEqRel A).

Global Instance A_has_bin_rel : HasBinRel A := eq_rel.

End Context.
