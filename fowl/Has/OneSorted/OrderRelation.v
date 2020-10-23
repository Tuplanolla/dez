From Maniunfold.Has Require Export
  OneSorted.BinaryRelation.

(** Order relation, less than or equality, precedence. *)

Class HasOrdRel (A : Type) : Type := ord_rel : A -> A -> Prop.

Typeclasses Transparent HasOrdRel.

Section Context.

Context {A : Type} `{HasOrdRel A}.

Global Instance A_has_bin_rel : HasBinRel A := ord_rel.

End Context.
