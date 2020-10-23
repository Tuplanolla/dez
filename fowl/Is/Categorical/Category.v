From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition Categorical.Identity.
From Maniunfold.Is Require Export
  Categorical.Semicategory Categorical.Unital.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

Class IsCat (A : Type) `{HasHom A}
  `(!HasComp hom) `(!HasIdt hom) : Prop := {
  A_comp_is_scat :> IsScat comp;
  A_comp_idt_is_cat_unl :> IsCatUnl comp idt;
}.
