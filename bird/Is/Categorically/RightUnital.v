(* bad *)
From Maniunfold.Has.Categorical Require Export
  Morphism Composition Identity.
From Maniunfold.ShouldHave.Categorical Require Import
  Notations.

Class IsCatRUnl {A : Type} {A_has_hom : HasHom A}
  (has_comp : HasComp hom) (has_idt : HasIdt hom) : Prop :=
  cat_r_unl : forall {x y : A} (f : x --> y), id o f = f.
