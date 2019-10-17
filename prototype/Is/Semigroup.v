From Maniunfold.Has Require Export
  EquivalenceRelation GroupOperation.
From Maniunfold.Is Require Export
  Proper Setoid Associative.

Import AdditiveNotations.

Class IsSemigroup {A : Type} {has_eqv : HasEqv A}
  (has_opr : HasOpr A) : Prop := {
  semigroup_opr_is_proper :> IsProper (eqv ==> eqv ==> eqv) opr;
  semigroup_opr_is_associative :> IsAssociative opr;
}.

Add Parametric Morphism {A : Type} `{is_semigroup : IsSemigroup A} : opr
  with signature eqv ==> eqv ==> eqv
  as eqv_opr_morphism.
Proof. apply semigroup_opr_is_proper; auto. Qed.
