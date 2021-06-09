(** * Equivalence Relation *)

From Maniunfold.Has Require Export
  BinaryRelation.

Class HasEqRel (A : Type) : Type := eq_rel : A -> A -> Prop.

Typeclasses Transparent HasEqRel.

Section Context.

Context (A : Type) `(HasEqRel A).

#[local] Instance has_bin_rel : HasBinRel A := eq_rel.

End Context.

#[export] Hint Resolve has_bin_rel : typeclass_instances.
