(** * Order Relation and Strict Order Relation *)

From Maniunfold.Has Require Export
  BinaryRelation.

Class HasOrdRel (A : Type) : Type := ord_rel (x y : A) : Prop.
Class HasStrOrdRel (A : Type) : Type := str_ord_rel (x y : A) : Prop.

Typeclasses Transparent HasOrdRel HasStrOrdRel.

Module Subclass.

Section Context.

Context (A : Type).

(** Order relations are binary relations. *)

#[local] Instance has_bin_rel
  (HR : HasOrdRel A) : HasBinRel A := ord_rel.

#[local] Instance str_has_bin_rel
  (HR : HasStrOrdRel A) : HasBinRel A := str_ord_rel.

End Context.

#[export] Hint Resolve has_bin_rel str_has_bin_rel : typeclass_instances.

End Subclass.
