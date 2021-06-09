(** * Apartness Relation, Constructive Inequality *)

From Maniunfold.Has Require Export
  BinaryRelation.

Class HasApartRel (A : Type) : Type := apart_rel (x y : A) : Prop.

Typeclasses Transparent HasApartRel.

Section Context.

Context (A : Type) `(HasApartRel A).

#[local] Instance has_bin_rel : HasBinRel A := apart_rel.

End Context.

#[export] Hint Resolve has_bin_rel : typeclass_instances.
