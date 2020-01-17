From Maniunfold.Has Require Export
  EquivalenceRelation.
From Maniunfold.Is Require Export
  Reflexive Symmetric Transitive.

Class IsSetoid {A : Type} (has_eq_rel : HasEqRel A) : Prop := {
  eq_rel_is_reflexive :> IsReflexive eq_rel;
  eq_rel_is_symmetric :> IsSymmetric eq_rel;
  eq_rel_is_transitive :> IsTransitive eq_rel;
}.

Section Context.

Context {A : Type} `{is_setoid : IsSetoid A}.

Global Instance eq_rel_equivalence : Equivalence eq_rel | 0 := {}.

End Context.
