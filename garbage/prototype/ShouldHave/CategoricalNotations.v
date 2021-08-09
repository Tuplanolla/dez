From DEZ.Has Require Export
  Arrow Composition Identity.
From DEZ.ShouldHave Require Export
  EquivalenceNotations.

Delimit Scope category_scope with category.

Open Scope category_scope.

Notation "g 'o' f" := (comp _ _ _ f g)
  (at level 38, left associativity) : category_scope.
Notation "'id'" := (iden _) : category_scope.
