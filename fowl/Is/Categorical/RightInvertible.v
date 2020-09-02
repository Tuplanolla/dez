From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition
  Categorical.Identity Categorical.Inverse.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

Class IsCatRInv (A : Type) {A_has_hom : HasHom A}
  (A_hom_has_comp : HasComp A hom) (A_hom_has_idt : HasIdt A hom)
  (A_hom_has_inv : HasInv A hom) : Prop :=
  cat_r_inv : forall {x y : A} (f : x --> y), f ^-1 o f = id.
