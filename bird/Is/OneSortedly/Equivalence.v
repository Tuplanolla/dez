From Coq Require Export
  Setoid Morphisms.
From Maniunfold.Has Require Export
  OneSorted.EquivalenceRelation.
From Maniunfold.Is Require Export
  Reflexive Symmetric Transitive.

Class IsEq {A : Type} (has_eq_rel : HasEqRel A) : Prop := {
  eq_rel_is_refl :> IsRefl eq_rel;
  eq_rel_is_sym :> IsSym eq_rel;
  eq_rel_is_trans :> IsTrans eq_rel;
}.

Section Context.

Context {A : Type} `{is_eq : IsEq A}.

Global Instance eq_rel_equivalence : Equivalence eq_rel | 0.
Proof. constructor; typeclasses eauto. Qed.

End Context.
