From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition Categorical.Identity.
From Maniunfold.Is Require Export
  Categorical.LeftUnital Categorical.RightUnital.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

Class IsCatUnl (A : Type) `{HasHom A}
  `(!HasComp hom) `(!HasIdt hom) : Prop := {
  A_comp_idt_is_cat_l_unl :> IsCatLUnl comp idt;
  A_comp_idt_is_cat_r_unl :> IsCatRUnl comp idt;
}.
