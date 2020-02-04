From Maniunfold.Has Require Export
  Composition Identity Inverse.
From Maniunfold.ShouldHave Require Export
  CategoricalNotations.

Declare Scope category_scope.

Delimit Scope category_scope with category.

Open Scope category_scope.

Reserved Notation "g 'o' f" (at level 38, left associativity).
Reserved Notation "'id'" (at level 0, no associativity).
Reserved Notation "f '^-1'" (at level 36, left associativity).

Notation "g 'o' f" := (comp _ _ _ f g) : category_scope.
Notation "'id'" := (idt _) : category_scope.
Notation "f '^-1'" := (inv _ _ f) : category_scope.
