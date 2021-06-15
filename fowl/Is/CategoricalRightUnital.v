From Maniunfold.Has Require Export
  Morphism ComposedMorphism IdentityMorphism.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class IsCatRUnl (A : Type) `(HasHom A) `(!HasCompHom hom) `(!HasIdHom hom) : Prop :=
  cat_r_unl : forall (x y : A) (f : x --> y), id o f = f.
