From Coq Require Import
  Setoid Morphisms.
From Maniunfold.Has.OneSorted Require Export
  EquivalenceRelation.
From Maniunfold.Is Require Export
  Symmetric Transitive.

Class IsPartEq {A : Type} (A_has_eq_rel : HasEqRel A) : Prop := {
  eq_rel_is_sym :> IsSym eq_rel;
  eq_rel_is_trans :> IsTrans eq_rel;
}.

Section Context.

Context {A : Type} `{is_part_eq : IsPartEq A}.

Global Instance eq_rel_p_e_r : PER eq_rel | 0.
Proof. split; typeclasses eauto. Qed.

End Context.
