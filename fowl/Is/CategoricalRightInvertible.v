From Maniunfold.Has Require Export
  Morphism ComposedMorphism
  IdentityMorphism InverseMorphism.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class IsCatRInv (A : Type) `(HasHom A)
  `(!HasCompHom hom) `(!HasIdHom hom) `(!HasInvHom hom) : Prop :=
  cat_r_inv_hom : forall (x y : A) (f : x --> y), f ^-1 o f = id.
