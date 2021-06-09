(** * Order Relation *)

From Maniunfold.Has Require Export
  BinaryRelation.

Class HasOrdRel (A : Type) : Type := ord_rel : A -> A -> Prop.

Typeclasses Transparent HasOrdRel.

Instance has_bin_rel (A : Type) `(HasOrdRel A) : HasBinRel A := ord_rel.

#[export] Hint Resolve has_bin_rel : typeclass_instances.
