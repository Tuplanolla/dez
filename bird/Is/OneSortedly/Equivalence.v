From Coq Require Export
  Setoid Morphisms.
From Maniunfold.Has Require Export
  EquivalenceRelation.
From Maniunfold.Is Require Export
  ReflexiveEquivalence SymmetricEquivalence TransitiveEquivalence.

Class IsEq {A : Type} (has_eq_rel : HasEqRel A) : Prop := {
  eq_rel_is_refl_eq :> IsReflEq eq_rel;
  eq_rel_is_sym_eq :> IsSymEq eq_rel;
  eq_rel_is_trans_eq :> IsTransEq eq_rel;
}.

Section Context.

Context {A : Type} `{is_eq : IsEq A}.

Global Instance eq_rel_equivalence : Equivalence eq_rel | 0 := {}.

End Context.
