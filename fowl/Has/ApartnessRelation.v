(** * Apartness Relation *)

From Maniunfold.Has Require Export
  BinaryRelation.

Class HasApartRel (A : Type) : Type := apart_rel (x y : A) : Prop.

Typeclasses Transparent HasApartRel.

Module Subclass.

Section Context.

Context (A : Type) (HR : HasApartRel A).

(** Apartness relation is a binary relation. *)

#[local] Instance has_bin_rel : HasBinRel A := apart_rel.

End Context.

#[export] Hint Resolve has_bin_rel : typeclass_instances.

End Subclass.
