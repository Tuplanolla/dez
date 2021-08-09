(** * Equivalence Relation *)

From DEZ.Has Require Export
  BinaryRelation.

Class HasEqRel (A : Type) : Type := eq_rel (x y : A) : Prop.

Typeclasses Transparent HasEqRel.

Module Subclass.

Section Context.

Context (A : Type) (HR : HasEqRel A).

(** Equivalence relation is a binary relation. *)

#[local] Instance has_bin_rel : HasBinRel A := eq_rel.

End Context.

#[export] Hint Resolve has_bin_rel : typeclass_instances.

End Subclass.
