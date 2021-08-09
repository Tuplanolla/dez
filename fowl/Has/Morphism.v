(** * Morphism or Hom-Set *)

From DEZ.Has Require Export
  BinaryRelation.

Class HasHom (A : Type) : Type := hom (x y : A) : Prop.

Typeclasses Transparent HasHom.

Module Subclass.

Section Context.

Context (A : Type) (HC : HasHom A).

(** Hom-set is a binary relation. *)

#[local] Instance has_bin_rel : HasBinRel A := hom.

End Context.

#[export] Hint Resolve has_bin_rel : typeclass_instances.

End Subclass.
