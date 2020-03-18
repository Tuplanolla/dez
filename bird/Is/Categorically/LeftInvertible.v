From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition
  Categorical.Identity Categorical.Inverse.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

Class IsCatLInv {A : Type} {A_has_hom : HasHom A}
  (has_comp : HasComp hom) (has_idt : HasIdt hom)
  (has_inv : HasInv hom) : Prop :=
  cat_l_inv : forall {x y : A} (f : x --> y), f o f ^-1 = id.
