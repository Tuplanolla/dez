From Maniunfold.Has Require Export
  Morphism ComposedMorphism IdentityMorphism.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class IsCatLUnl (A : Type) `(HasHom A) `(!HasCompHom hom) `(!HasIdHom hom) : Prop :=
  cat_l_unl : forall (x y : A) (f : x --> y), f o id = f.
