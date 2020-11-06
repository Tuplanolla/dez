From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition.

Class IsMagd (A : Type) `(HasHom A)
  `(HasComp A) : Prop := {}.
