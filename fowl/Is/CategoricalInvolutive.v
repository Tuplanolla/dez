From Maniunfold.Has Require Export
  CategoricalMorphism CategoricalInverse.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class IsCatInvol (A : Type) `(HasHom A) `(!HasInv hom) : Prop :=
  cat_invol : forall (x y : A) (f : x --> y), (f ^-1) ^-1 = f.
