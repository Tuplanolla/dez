(** * Operational class for order relations. *)

From Maniunfold.Has Require Export
  OneSortedBinaryRelation.

Class HasOrdRel (A : Type) : Type := ord_rel : A -> A -> Prop.

#[export] Hint Transparent HasOrdRel : typeclass_instances.

Instance has_bin_rel (A : Type) `(HasOrdRel A) : HasBinRel A := ord_rel.

#[export] Hint Resolve has_bin_rel : typeclass_instances.
