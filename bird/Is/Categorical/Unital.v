From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition Categorical.Identity.
From Maniunfold.Is Require Export
  Categorical.LeftUnital Categorical.RightUnital.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

Class IsCatUnl (A : Type) {A_has_hom : HasHom A}
  (A_hom_has_comp : HasComp A hom) (A_hom_has_idt : HasIdt A hom) : Prop := {
  A_comp_idt_is_cat_l_unl :> IsCatLUnl A comp idt;
  A_comp_idt_is_cat_r_unl :> IsCatRUnl A comp idt;
}.
