From Maniunfold.Has Require Export
  Morphism EquivalenceRelation Composition.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations MoreCategoricalNotations.

Class IsCatAssoc {A : Type} {has_hom : HasHom A}
  {has_eq_rel : forall x y : A, HasEqRel (x ~> y)}
  (has_comp : HasComp hom) : Prop :=
  cat_assoc : forall {x y z w : A} (f : x ~> y) (g : y ~> z) (h : z ~> w),
    (h o g) o f == h o (g o f).
