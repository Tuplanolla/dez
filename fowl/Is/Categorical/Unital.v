From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition Categorical.Identity.
From Maniunfold.Is Require Export
  Categorical.LeftUnital Categorical.RightUnital.

Class IsCatUnl (A : Type)
  `(HasHom A) `(!HasComp hom) `(!HasIdt hom) : Prop := {
  hom_comp_idn_is_cat_l_unl :> IsCatLUnl hom comp idn;
  hom_comp_idn_is_cat_r_unl :> IsCatRUnl hom comp idn;
}.
