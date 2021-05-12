From Maniunfold.Has Require Export
  CategoricalMorphism CategoricalComposition.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class IsCatAssoc (A : Type) `(HasHom A) `(!HasComp hom) : Prop :=
  cat_assoc : forall (x y z w : A) (f : x --> y) (g : y --> z) (h : z --> w),
    (h o g) o f = h o (g o f).
