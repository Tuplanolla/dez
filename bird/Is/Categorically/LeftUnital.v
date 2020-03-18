From Maniunfold.Has.Categorical Require Export
  Morphism Composition Identity.
From Maniunfold.ShouldHave.Categorical Require Import
  Notations.

Class IsCatLUnl {A : Type} {A_has_hom : HasHom A}
  (has_comp : HasComp hom) (has_idt : HasIdt hom) : Prop :=
  cat_l_unl : forall {x y : A} (f : x --> y), f o id = f.
