From Maniunfold.Has Require Export
  Morphism ComposedMorphism
  IdentityMorphism InverseMorphism.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class IsCatLInv (A : Type) `(HasHom A)
  `(!HasCompHom hom) `(!HasIdHom hom) `(!HasInvHom hom) : Prop :=
  cat_l_inv_hom : forall (x y : A) (f : x --> y), f o f ^-1 = id.
