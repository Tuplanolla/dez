(** * Properties of Orders *)

From DEZ.Has Require Export
  OrderRelations.
From DEZ.ShouldHave Require Import
  OrderRelationNotations.

(** Orders and strict orders can be defined in terms of each other. *)

Module ToStrict.

Section Context.

Context (A : Type) (R : HasOrdRel A).

(** This has the same shape as [le_neq]. *)

Equations str_ord_rel_def (x y : A) : Prop :=
  str_ord_rel_def x y := x <= y /\ x <> y.

#[local] Instance has_str_ord_rel : HasStrOrdRel A := str_ord_rel_def.

End Context.

#[export] Hint Resolve has_str_ord_rel : typeclass_instances.

End ToStrict.

Module FromStrict.

Section Context.

Context (A : Type) (R : HasStrOrdRel A).

(** This has the same shape as [le_lteq]. *)

Equations ord_rel_def (x y : A) : Prop :=
  ord_rel_def x y := x < y \/ x = y.

#[local] Instance has_ord_rel : HasOrdRel A := ord_rel_def.

End Context.

#[export] Hint Resolve has_ord_rel : typeclass_instances.

End FromStrict.
