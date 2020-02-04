From Maniunfold.Has Require Export
  Morphism EquivalenceRelation Composition Identity Inverse.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations MoreCategoricalNotations.

Class IsCatLInv {A : Type} {has_hom : HasHom A}
  {has_eq_rel : forall x y : A, HasEqRel (x ~> y)}
  (has_comp : HasComp hom) (has_idt : HasIdt hom)
  (has_inv : HasInv hom) : Prop :=
  cat_l_inv : forall {x y : A} (f : x ~> y), f o f ^-1 == id.
