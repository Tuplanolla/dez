From Maniunfold.Has Require Export
  CategoricalMorphism CategoricalComposition
  CategoricalIdentity CategoricalInverse.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class IsCatLInv (A : Type) `(HasHom A)
  `(!HasComp hom) `(!HasIdt hom) `(!HasInv hom) : Prop :=
  cat_l_inv : forall (x y : A) (f : x --> y), f o f ^-1 = id.
