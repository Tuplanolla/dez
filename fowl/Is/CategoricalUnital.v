From DEZ.Has Require Export
  Morphism ComposedMorphism IdentityMorphism.
From DEZ.Is Require Export
  CategoricalLeftUnital CategoricalRightUnital.

Class IsCatUnl (A : Type)
  `(HasHom A) `(!HasCompHom hom) `(!HasIdHom hom) : Prop := {
  comp_hom_id_hom_is_cat_unl_l :> IsCatUnlL comp_hom id_hom;
  comp_hom_id_hom_is_cat_unl_r :> IsCatUnlR comp_hom id_hom;
}.
