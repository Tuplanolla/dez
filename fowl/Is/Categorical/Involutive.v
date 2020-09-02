From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Inverse.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

Class IsCatInvol (A : Type) {A_has_hom : HasHom A}
  (A_hom_has_inv : HasInv A hom) : Prop :=
  cat_invol : forall {x y : A} (f : x --> y), (f ^-1) ^-1 = f.
