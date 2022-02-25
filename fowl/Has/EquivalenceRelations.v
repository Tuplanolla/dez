(** * Equivalences *)

From DEZ.Has Require Export
  Relations.

(** ** Equivalence Relation *)

Class HasEquivRel (A : Type) : Type := equiv_rel (x y : A) : Prop.

#[export] Typeclasses Transparent HasEquivRel.

Module Subclass.

Section Context.

Context (A : Type).

(** Equivalence relation is a binary relation. *)

#[export] Instance equiv_rel_has_bin_rel {X : HasEquivRel A} : HasBinRel A :=
  equiv_rel.

End Context.

End Subclass.
