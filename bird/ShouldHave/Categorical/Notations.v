From Maniunfold.Has Require Export
  Categorical.Composition Categorical.Identity Categorical.Inverse.
From Maniunfold.ShouldHave Require Export
  Categorical.TypeNotations.

Reserved Notation "g 'o' f" (at level 38, left associativity).
Reserved Notation "'id'" (at level 0, no associativity).
Reserved Notation "f '^-1'" (at level 36, left associativity).

Notation "g 'o' f" := (comp _ _ _ f g) : cat_scope.
Notation "'id'" := (idt _) : cat_scope.
Notation "f '^-1'" := (inv _ _ f) : cat_scope.
