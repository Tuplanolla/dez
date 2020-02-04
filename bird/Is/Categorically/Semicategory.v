From Maniunfold.Has Require Export
  Morphism EquivalenceRelation Composition.
From Maniunfold.Is Require Export
  Magmoid CategoricallyAssociative.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class IsScat {A : Type} {has_hom : HasHom A}
  {has_eq_rel : forall x y : A, HasEqRel (x ~> y)}
  (has_comp : HasComp hom) : Prop := {
  comp_is_magd :> IsMagd comp;
  comp_is_cat_assoc :> IsCatAssoc comp;
}.
