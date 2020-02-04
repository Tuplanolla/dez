From Maniunfold.Has Require Export
  Morphism EquivalenceRelation Composition Identity.
From Maniunfold.Is Require Export
  CategoricallyLeftUnital CategoricallyRightUnital.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class IsCatUnl {A : Type} {has_hom : HasHom A}
  {has_eq_rel : forall x y : A, HasEqRel (x ~> y)}
  (has_comp : HasComp hom) (has_idt : HasIdt hom) : Prop := {
  comp_idt_is_l_cat_unl :> IsCatLUnl comp idt;
  comp_idt_is_r_cat_unl :> IsCatRUnl comp idt;
}.
