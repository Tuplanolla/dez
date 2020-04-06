(* bad *)
From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition.

Class IsMagd {A : Type} {A_has_hom : HasHom A}
  (has_comp : HasComp hom) : Prop := {}.
