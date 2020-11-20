From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition Categorical.Identity.
From Maniunfold.Is Require Export
  Categorical.Semicategory Categorical.Unital.

Class IsCat (A : Type) `(HasHom A) `(!HasComp hom) `(!HasIdt hom) : Prop := {
  comp_is_scat :> IsScat comp;
  comp_idn_is_cat_unl :> IsCatUnl comp idn;
}.
