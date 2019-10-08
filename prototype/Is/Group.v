From Maniunfold.Has Require Import EquivalenceRelation
  GroupOperation GroupIdentity GroupInverse.
From Maniunfold.Is Require Import Setoid Monoid Inverse.

Import AdditiveNotations.

Class IsGroup (A : Type) {has_eqv : HasEqv A}
  {has_opr : HasOpr A} {has_idn : HasIdn A} {has_inv : HasInv A} : Prop := {
  inv_proper : inv ::> eqv ==> eqv;
  opr_is_monoid :> IsMonoid A;
  opr_is_inverse :> IsInverse A;
}.

Add Parametric Morphism {A : Type} `{is_group : IsGroup A} : inv
  with signature eqv ==> eqv
  as eqv_inv_morphism.
Proof. intros x y p. apply inv_proper; auto. Qed.
