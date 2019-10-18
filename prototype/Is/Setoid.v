From Maniunfold.Has Require Export
  EquivalenceRelation.
From Maniunfold.Is Require Export
  Reflexive Symmetric Transitive.

Class IsSetoid {A : Type} (has_eqv : HasEqv A) : Prop := {
  setoid_is_reflexive :> IsReflexive eqv;
  setoid_is_symmetric :> IsSymmetric eqv;
  setoid_is_transitive :> IsTransitive eqv;
}.

Section Context.

Context {A : Type} `{is_setoid : IsSetoid A}.

Global Instance setoid_is_equivalence : Equivalence eqv := {}.
Global Instance setoid_is_rewrite_relation : RewriteRelation eqv := {}.

End Context.
