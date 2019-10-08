From Maniunfold.Has Require Import EquivalenceRelation GroupOperation.
From Maniunfold.Is Require Import Setoid Associative.

Import AdditiveNotations.

Class IsSemigroup (A : Type)
  {has_eqv : HasEqv A} {has_opr : HasOpr A} : Prop := {
  opr_proper : opr ::> eqv ==> eqv ==> eqv;
  opr_is_associative :> IsAssociative A;
}.

Add Parametric Morphism {A : Type} `{is_semigroup : IsSemigroup A} : opr
  with signature eqv ==> eqv ==> eqv
  as eqv_opr_morphism.
Proof. intros x y p z w q. apply opr_proper; auto. Qed.
