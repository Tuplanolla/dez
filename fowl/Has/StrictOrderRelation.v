(** * Operational class for strict order relations. *)

From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.

Class HasStrictOrdRel (A : Type) : Type := strict_ord_rel : A -> A -> Prop.

#[export] Hint Transparent HasStrictOrdRel : typeclass_instances.

Instance has_bin_rel (A : Type) `(HasStrictOrdRel A) : HasBinRel A :=
  strict_ord_rel.

#[export] Hint Resolve has_bin_rel : typeclass_instances.
