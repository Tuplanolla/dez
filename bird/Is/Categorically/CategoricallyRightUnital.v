From Maniunfold.Has Require Export
  Morphism EquivalenceRelation Composition Identity.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations MoreCategoricalNotations.

Class IsCatRUnl {A : Type} {has_hom : HasHom A}
  {has_eq_rel : forall x y : A, HasEqRel (x ~> y)}
  (has_comp : HasComp hom) (has_idt : HasIdt hom) : Prop :=
  cat_r_unl : forall {x y : A} (f : x ~> y), id o f == f.
