From Maniunfold.Has Require Export
  Morphism EquivalenceRelation Composition Identity.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations MoreCategoricalNotations.

Class IsCatLUnl {A : Type} {has_hom : HasHom A}
  {has_eq_rel : forall x y : A, HasEqRel (x ~> y)}
  (has_comp : HasComp hom) (has_idt : HasIdt hom) : Prop :=
  cat_l_unl : forall {x y : A} (f : x ~> y), f o id == f.
