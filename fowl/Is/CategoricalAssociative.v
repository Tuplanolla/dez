From Maniunfold.Has Require Export
  Morphism ComposedMorphism.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class IsCatAssoc (A : Type) `(HasHom A) `(!HasCompHom hom) : Prop :=
  cat_assoc : forall (x y z w : A) (f : x --> y) (g : y --> z) (h : z --> w),
    (h o g) o f = h o (g o f).
