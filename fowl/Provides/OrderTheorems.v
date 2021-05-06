(** * Order theory. *)

From Maniunfold.Has Require Export
  OrderRelation StrictOrderRelation.
From Maniunfold.ShouldHave Require Import
  OrderRelationNotations StrictOrderRelationNotations.

(** Orders and strict orders can be defined in terms of each other. *)

Module StrictFromLax.

Section Context.

Context (A : Type) `(HasOrdRel A).

(** We use the same argument order to [/\] as [le_neq]. *)

Equations strict_ord_rel_def (x y : A) : Prop :=
  strict_ord_rel_def x y := x <= y /\ x <> y.

Instance has_strict_ord_rel : HasStrictOrdRel A := strict_ord_rel_def.

End Context.

#[export] Hint Resolve has_strict_ord_rel : typeclass_instances.

End StrictFromLax.

Module LaxFromStrict.

Section Context.

Context (A : Type) `(HasStrictOrdRel A).

(** We use the same argument order to [\/] as [le_lteq]. *)

Equations ord_rel_def (x y : A) : Prop :=
  ord_rel_def x y := x < y \/ x = y.

Instance has_ord_rel : HasOrdRel A := ord_rel_def.

End Context.

#[export] Hint Resolve has_ord_rel : typeclass_instances.

End LaxFromStrict.