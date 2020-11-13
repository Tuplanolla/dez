From Maniunfold.Has Require Export
  Categorical.Composition Categorical.Identity Categorical.Inverse.
From Maniunfold.ShouldHave Require Export
  Categorical.TypeNotations.

Declare Scope cat_scope.

Delimit Scope cat_scope with cat.

Open Scope cat_scope.

Notation "g 'o' f" := (comp _ _ _ f g) : cat_scope.
Notation "'id'" := (idn _) : cat_scope.
Notation "f '^-1'" := (inv _ _ f) : cat_scope.

Notation "'_o_'" := (comp _ _ _) (only parsing) : cat_scope.
Notation "'_^-1'" := (inv _ _) (only parsing) : cat_scope.
