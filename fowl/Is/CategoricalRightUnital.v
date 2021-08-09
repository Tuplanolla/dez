From DEZ.Has Require Export
  Morphism ComposedMorphism IdentityMorphism.
From DEZ.ShouldHave Require Import
  CategoricalNotations.

Class IsCatUnlR (A : Type) `(HasHom A) `(!HasCompHom hom) `(!HasIdHom hom) : Prop :=
  cat_unl_r : forall (x y : A) (f : x --> y), id o f = f.
