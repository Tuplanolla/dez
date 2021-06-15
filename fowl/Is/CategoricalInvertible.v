From Maniunfold.Has Require Export
  Morphism ComposedMorphism IdentityMorphism
  InverseMorphism.
From Maniunfold.Is Require Export
  CategoricalLeftInvertible CategoricalRightInvertible.

Class IsCatInv (A : Type)
  `(HasHom A) `(!HasCompHom hom) `(!HasIdHom hom) `(!HasInvHom hom) : Prop := {
  comp_hom_id_hom_inv_hom_is_cat_l_inv_hom :> IsCatLInv comp_hom id_hom inv_hom;
  comp_hom_id_hom_inv_hom_is_cat_r_inv_hom :> IsCatRInv comp_hom id_hom inv_hom;
}.
