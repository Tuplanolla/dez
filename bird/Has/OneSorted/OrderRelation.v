From Maniunfold.Has Require Export
  OneSorted.EquivalenceRelation.

Class HasOrdRel (A : Type) : Type := ord_rel : A -> A -> Prop.

Typeclasses Transparent HasOrdRel.

Section Context.

Context {A : Type} `{has_ord_rel : HasOrdRel A}.

Global Instance A_has_eq_rel : HasEqRel A := ord_rel.

End Context.
