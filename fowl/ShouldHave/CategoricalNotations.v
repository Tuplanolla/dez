(** * Indexed Notations for Categories *)

From Maniunfold.Has Require Import
  ComposedMorphism IdentityMorphism InverseMorphism.
From Maniunfold.ShouldHave Require Export
  MorphismNotations.

Notation "'_o_'" := (comp_hom _ _ _) : category_scope.
Notation "g 'o' f" := (comp_hom _ _ _ g f) : category_scope.
Notation "'_^-1'" := (inv_hom _ _) : category_scope.
Notation "f '^-1'" := (inv_hom _ _ f) : category_scope.
Notation "'id'" := (id_hom _) : category_scope.
