From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition Categorical.Identity.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

Class IsCatRUnl (A : Type) {A_has_hom : HasHom A}
  (A_hom_has_comp : HasComp A hom) (A_hom_has_idt : HasIdt A hom) : Prop :=
  cat_r_unl : forall {x y : A} (f : x --> y), id o f = f.
