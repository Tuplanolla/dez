From Maniunfold.Has Require Export
  CategoricalMorphism CategoricalComposition CategoricalIdentity.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class IsCatRUnl (A : Type) `(HasHom A) `(!HasComp hom) `(!HasIdt hom) : Prop :=
  cat_r_unl : forall (x y : A) (f : x --> y), id o f = f.
