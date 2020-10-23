From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition Categorical.Identity.
From Maniunfold.Is Require Export
  Categorical.LeftUnital Categorical.RightUnital.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

Class IsCatUnl (A : Type) `{HasHom A}
  `(!HasComp A hom) `(!HasIdt A hom) : Prop := {
  A_comp_idt_is_cat_l_unl :> IsCatLUnl A comp idt;
  A_comp_idt_is_cat_r_unl :> IsCatRUnl A comp idt;
}.
