(* bad *)
From Maniunfold.Has.Categorical Require Export
  Morphism Composition Identity.
From Maniunfold.Is.Categorically Require Export
  Semicategory Unital.
From Maniunfold.ShouldHave.Categorical Require Import
  Notations.

Class IsCat {A : Type} {A_has_hom : HasHom A}
  (has_comp : HasComp hom) (has_idt : HasIdt hom) : Prop := {
  comp_is_scat :> IsScat comp;
  comp_idt_is_cat_unl :> IsCatUnl comp idt;
}.
