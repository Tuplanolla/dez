From Maniunfold.Has Require Export
  Morphism ComposedMorphism IdentityMorphism.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class IsCatUnlL (A : Type) `(HasHom A) `(!HasCompHom hom) `(!HasIdHom hom) : Prop :=
  cat_unl_l : forall (x y : A) (f : x --> y), f o id = f.
