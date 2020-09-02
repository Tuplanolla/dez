From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

Class IsCatAssoc (A : Type) {A_has_hom : HasHom A}
  (A_hom_has_comp : HasComp A hom) : Prop :=
  cat_assoc : forall {x y z w : A} (f : x --> y) (g : y --> z) (h : z --> w),
    (h o g) o f = h o (g o f).
