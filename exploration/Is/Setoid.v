From Maniunfold.Has Require Export
  EquivalenceRelation.
From Maniunfold.Is Require Export
  Reflexive Symmetric Transitive.

Class IsSetoid {A : Type} (has_eqv : HasEqv A) : Prop := {
  eqv_is_reflexive :> IsReflexive eqv;
  eqv_is_symmetric :> IsSymmetric eqv;
  eqv_is_transitive :> IsTransitive eqv;
}.

Section Context.

Context {A : Type} `{is_setoid : IsSetoid A}.

Global Instance eqv_equivalence : Equivalence eqv | 0 := {}.

End Context.
