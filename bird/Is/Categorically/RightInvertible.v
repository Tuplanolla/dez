From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition
  Categorical.Identity Categorical.Inverse.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

Class IsCatRInv {A : Type} {has_hom : HasHom A}
  (has_comp : HasComp hom) (has_idt : HasIdt hom)
  (has_inv : HasInv hom) : Prop :=
  cat_r_inv : forall {x y : A} (f : x --> y), f ^-1 o f = id.
