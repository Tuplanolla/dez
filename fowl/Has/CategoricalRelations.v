(** * Categorical Relations *)

From DEZ.Has Require Export
  Relations.

(** ** Hom-Set *)
(** ** Morphism *)

Class HasHom (A : Type) : Type := hom (x y : A) : Prop.

#[export] Typeclasses Transparent HasHom.

Module Subclass.

Section Context.

Context (A : Type).

(** A hom-set is a binary relation between objects. *)

#[export] Instance hom_has_bin_rel {X : HasHom A} : HasBinRel A := hom.

End Context.

End Subclass.
