From DEZ.Has Require Export
  Morphism ComposedMorphism.
From DEZ.Supports Require Import
  CategoricalNotations.

Class IsCatAssoc (A : Type) `(HasHom A) `(!HasCompHom hom) : Prop :=
  cat_assoc : forall (x y z w : A) (f : x --> y) (g : y --> z) (h : z --> w),
    (h o g) o f = h o (g o f).
