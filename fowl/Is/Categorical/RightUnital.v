From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition Categorical.Identity.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

Class IsCatRUnl (A : Type) `(HasHom A) `(!HasComp hom) `(!HasIdt hom) : Prop :=
  cat_r_unl : forall {x y : A} (f : x --> y), id o f = f.
