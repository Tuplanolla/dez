(** * Orders *)

From DEZ.Has Require Export
  Relations.

(** ** Order Relation *)

Class HasOrdRel (A : Type) : Type := ord_rel (x y : A) : Prop.

#[export] Typeclasses Transparent HasOrdRel.

(** ** Strict Order Relation *)

Class HasStrOrdRel (A : Type) : Type := str_ord_rel (x y : A) : Prop.

#[export] Typeclasses Transparent HasStrOrdRel.

Module Subclass.

Section Context.

Context (A : Type).

(** An order relation is a binary relation. *)

#[export] Instance ord_rel_has_bin_rel
  {X : HasOrdRel A} : HasBinRel A := ord_rel.

(** A strict order relation is a binary relation. *)

#[export] Instance str_ord_rel_has_bin_rel
  {X : HasStrOrdRel A} : HasBinRel A := str_ord_rel.

End Context.

End Subclass.
