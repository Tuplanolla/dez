(* bad *)
From Maniunfold.Has.Categorical Require Export
  Morphism Inverse.
From Maniunfold.ShouldHave.Categorical Require Import
  Notations.

Class IsCatInvol {A : Type} {A_has_hom : HasHom A}
  (has_inv : HasInv hom) : Prop :=
  cat_invol : forall {x y : A} (f : x --> y), (f ^-1) ^-1 = f.
