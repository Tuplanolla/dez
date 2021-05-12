From Maniunfold.Has Require Export
  CategoricalMorphism CategoricalComposition CategoricalIdentity.
From Maniunfold.Is Require Export
  CategoricalLeftUnital CategoricalRightUnital.

Class IsCatUnl (A : Type)
  `(HasHom A) `(!HasComp hom) `(!HasIdt hom) : Prop := {
  comp_idn_is_cat_l_unl :> IsCatLUnl comp idn;
  comp_idn_is_cat_r_unl :> IsCatRUnl comp idn;
}.
