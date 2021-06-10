(** * Order Relation *)

From Maniunfold.Has Require Export
  BinaryRelation.

Class HasOrdRel (A : Type) : Type := ord_rel (x y : A) : Prop.

Typeclasses Transparent HasOrdRel.

Section Context.

Context (A : Type) (R : HasOrdRel A).

#[local] Instance has_bin_rel : HasBinRel A := ord_rel.

End Context.

#[export] Hint Resolve has_bin_rel : typeclass_instances.
