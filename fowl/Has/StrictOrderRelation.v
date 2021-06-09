(** * Strict Order Relations *)

From Maniunfold.Has Require Export
  BinaryRelation.

Class HasStrOrdRel (A : Type) : Type := str_ord_rel (x y : A) : Prop.

Section Context.

Context (A : Type) `(HasStrOrdRel A).

#[local] Instance has_bin_rel : HasBinRel A := str_ord_rel.

End Context.

#[export] Hint Resolve has_bin_rel : typeclass_instances.
