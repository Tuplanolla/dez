From Maniunfold.Has Require Export
  CategoricalMorphism CategoricalComposition CategoricalIdentity.
From Maniunfold.Is Require Export
  CategoricalSemicategory CategoricalUnital.

Class IsCat (A : Type) `(HasHom A) `(!HasComp hom) `(!HasIdt hom) : Prop := {
  comp_is_scat :> IsScat comp;
  comp_idn_is_cat_unl :> IsCatUnl comp idn;
}.
