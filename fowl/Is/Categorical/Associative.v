From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

Class IsCatAssoc (A : Type) `(HasHom A)
  `(HasComp A) : Prop :=
  cat_assoc : forall {x y z w : A} (f : x --> y) (g : y --> z) (h : z --> w),
    (h o g) o f = h o (g o f).
