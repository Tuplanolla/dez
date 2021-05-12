From Maniunfold.Has Require Export
  CategoricalMorphism CategoricalComposition
  CategoricalIdentity CategoricalInverse.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class IsCatRInv (A : Type) `(HasHom A)
  `(!HasComp hom) `(!HasIdt hom) `(!HasInv hom) : Prop :=
  cat_r_inv : forall (x y : A) (f : x --> y), f ^-1 o f = id.
