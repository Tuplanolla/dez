From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Inverse.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

Class IsCatInvol (A : Type) `(HasHom A)
  `(!HasInv hom) : Prop :=
  cat_invol : forall {x y : A} (f : x --> y), (f ^-1) ^-1 = f.
