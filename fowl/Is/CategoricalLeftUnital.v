From Maniunfold.Has Require Export
  CategoricalMorphism CategoricalComposition CategoricalIdentity.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class IsCatLUnl (A : Type) `(HasHom A) `(!HasComp hom) `(!HasIdt hom) : Prop :=
  cat_l_unl : forall (x y : A) (f : x --> y), f o id = f.
