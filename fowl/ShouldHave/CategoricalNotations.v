From Maniunfold.Has Require Export
  ComposedMorphism IdentityMorphism InverseMorphism.
From Maniunfold.ShouldHave Require Export
  MorphismNotations.

Declare Scope category_scope.
Delimit Scope category_scope with cat.

Notation "'_o_'" := (comp_hom _ _ _) : cat.
Notation "g 'o' f" := (comp_hom _ _ _ g f) : cat.
Notation "'id'" := (id_hom _) : cat.
Notation "'_^-1'" := (inv_hom _ _) : cat.
Notation "f '^-1'" := (inv_hom _ _ f) : cat.

#[global] Open Scope cat.
