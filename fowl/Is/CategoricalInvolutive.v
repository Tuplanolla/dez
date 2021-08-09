From DEZ.Has Require Export
  Morphism InverseMorphism.
From DEZ.ShouldHave Require Import
  CategoricalNotations.

Class IsCatInvol (A : Type) `(HasHom A) `(!HasInvHom hom) : Prop :=
  cat_invol : forall (x y : A) (f : x --> y), (f ^-1) ^-1 = f.
