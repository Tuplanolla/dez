From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition.
From Maniunfold.Is Require Export
  Categorical.Associative Categorical.Magmoid.

Class IsScat (A : Type) `(HasHom A) `(!HasComp hom) : Prop := {
  comp_is_cat_assoc :> IsCatAssoc comp;
  comp_is_magd :> IsMagd comp;
}.
