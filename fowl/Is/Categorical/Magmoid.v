From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition.

Class IsMagd (A : Type) {A_has_hom : HasHom A}
  (A_hom_has_comp : HasComp A hom) : Prop := {}.
