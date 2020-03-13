From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition.

Class IsMagd {A : Type} {has_hom : HasHom A}
  (has_comp : HasComp hom) : Prop := {}.
