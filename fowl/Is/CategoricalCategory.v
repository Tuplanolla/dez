From DEZ.Has Require Export
  Morphism ComposedMorphism IdentityMorphism.
From DEZ.Is Require Export
  CategoricalSemicategory CategoricalUnital.

Class IsCat (A : Type) `(HasHom A) `(!HasCompHom hom) `(!HasIdHom hom) : Prop := {
  comp_hom_is_scat :> IsSemicat comp_hom;
  comp_hom_id_hom_is_cat_unl :> IsCatUnl comp_hom id_hom;
}.
