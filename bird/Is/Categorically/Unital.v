From Maniunfold.Has.Categorical Require Export
  Morphism Composition Identity.
From Maniunfold.Is.Categorically Require Export
  LeftUnital RightUnital.
From Maniunfold.ShouldHave.Categorical Require Import
  Notations.

Class IsCatUnl {A : Type} {A_has_hom : HasHom A}
  (has_comp : HasComp hom) (has_idt : HasIdt hom) : Prop := {
  comp_idt_is_cat_l_unl :> IsCatLUnl comp idt;
  comp_idt_is_cat_r_unl :> IsCatRUnl comp idt;
}.
