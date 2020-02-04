From Maniunfold.Has Require Export
  Morphism EquivalenceRelation Composition Identity.
From Maniunfold.Is Require Export
  Semicategory CategoricallyUnital.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class IsCat {A : Type} {has_hom : HasHom A}
  {has_eq_rel : forall x y : A, HasEqRel (x ~> y)}
  (has_comp : HasComp hom) (has_idt : HasIdt hom) : Prop := {
  comp_is_scat :> IsScat comp;
  comp_idt_is_cat_unl :> IsCatUnl comp idt;
}.
