From Maniunfold.Has Require Export
  Morphism ComposedMorphism IdentityMorphism
  InverseMorphism.
From Maniunfold.Is Require Export
  CategoricalCategory CategoricalInvertible CategoricalInvolutive.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class IsGrpd (A : Type)
  `(HasHom A) `(!HasCompHom hom) `(!HasIdHom hom) `(!HasInvHom hom) : Prop := {
  comp_hom_id_hom_is_cat :> IsCat comp_hom id_hom;
  comp_hom_id_hom_inv_hom_is_cat_inv_hom :> IsCatInvLR id_hom inv_hom comp_hom;
}.

Section Context.

Context (A : Type) `{IsGrpd A}.

Theorem inv_hom_cat_invol (x y : A) (f : x --> y) : (f ^-1) ^-1 = f.
Proof.
  rewrite <- (cat_unl_r _ _ ((f ^-1) ^-1)).
  rewrite <- (cat_inv_l _ _ f).
  rewrite (cat_assoc _ _ _ _ ((f ^-1) ^-1) (f ^-1) f).
  rewrite (cat_inv_l _ _ (f ^-1)).
  rewrite (cat_unl_l _ _ f).
  reflexivity. Qed.

Global Instance inv_hom_is_cat_invol : IsCatInvol inv_hom.
Proof. exact @inv_hom_cat_invol. Qed.

End Context.
