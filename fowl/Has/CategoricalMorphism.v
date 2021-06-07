From Maniunfold.Has Require Export
  BinaryRelation.

(** Morphism, arrow.
    Commonly found in categories. *)

Class HasHom (A : Type) : Type := hom : A -> A -> Prop.

Typeclasses Transparent HasHom.

Section Context.

Context (A : Type) `(HasHom A).

Global Instance A_has_bin_rel : HasBinRel A := hom.

End Context.
