From Maniunfold.Has Require Export
  Morphism ComposedMorphism IdentityMorphism.
From Maniunfold.Is Require Export
  CategoricalLeftUnital CategoricalRightUnital.

Class IsCatUnl (A : Type)
  `(HasHom A) `(!HasCompHom hom) `(!HasIdHom hom) : Prop := {
  comp_hom_id_hom_is_cat_l_unl :> IsCatLUnl comp_hom id_hom;
  comp_hom_id_hom_is_cat_r_unl :> IsCatRUnl comp_hom id_hom;
}.
