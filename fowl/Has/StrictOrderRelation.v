(** * Strict Order Relations *)

From Maniunfold.Has Require Export
  BinaryRelation.

Class HasStrOrdRel (A : Type) : Type := str_ord_rel : A -> A -> Prop.

Typeclasses Transparent HasStrOrdRel.

Instance has_bin_rel (A : Type) `(HasStrOrdRel A) : HasBinRel A :=
  str_ord_rel.

#[export] Hint Resolve has_bin_rel : typeclass_instances.
