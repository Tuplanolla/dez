From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition
  Categorical.Identity Categorical.Inverse.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

Class IsCatRInv (A : Type) `{HasHom A}
  `(!HasComp A hom) `(!HasIdt A hom)
  `(!HasInv A hom) : Prop :=
  cat_r_inv : forall {x y : A} (f : x --> y), f ^-1 o f = id.
