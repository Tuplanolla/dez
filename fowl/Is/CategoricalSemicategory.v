From Maniunfold.Has Require Export
  CategoricalMorphism CategoricalComposition.
From Maniunfold.Is Require Export
  CategoricalAssociative CategoricalMagmoid.

Class IsScat (A : Type) `(HasHom A) `(!HasComp hom) : Prop := {
  comp_is_cat_assoc :> IsCatAssoc comp;
  comp_is_magd :> IsMagd comp;
}.
