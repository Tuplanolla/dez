From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition
  Categorical.Identity Categorical.Inverse.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

Class IsCatLInv (A : Type) `(HasHom A)
  `(!HasComp hom) `(!HasIdt hom)
  `(!HasInv hom) : Prop :=
  cat_l_inv : forall {x y : A} (f : x --> y), f o f ^-1 = id.
