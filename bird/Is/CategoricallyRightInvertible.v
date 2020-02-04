From Maniunfold.Has Require Export
  Morphism EquivalenceRelation Composition Identity Inverse.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations CategoricalNotations.
From Maniunfold.ShouldOffer Require Import
  MoreCategoricalNotations.

Class IsCatRInv {A : Type} {has_hom : HasHom A}
  {has_eq_rel : forall x y : A, HasEqRel (x ~> y)}
  (has_comp : HasComp hom) (has_idt : HasIdt hom)
  (has_inv : HasInv hom) : Prop :=
  cat_r_inv : forall {x y : A} (f : x ~> y), f ^-1 o f == id.
