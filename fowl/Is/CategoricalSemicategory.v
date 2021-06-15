From Maniunfold.Has Require Export
  Morphism ComposedMorphism.
From Maniunfold.Is Require Export
  CategoricalAssociative CategoricalMagmoid.

Class IsSemicat (A : Type) `(HasHom A) `(!HasCompHom hom) : Prop := {
  comp_hom_is_cat_assoc :> IsCatAssoc comp_hom;
  comp_hom_is_magd :> IsMagd comp_hom;
}.
