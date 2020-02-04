From Maniunfold.Has Require Export
  Morphism EquivalenceRelation Composition Identity Inverse.
From Maniunfold.Is Require Export
  CategoricallyLeftInvertible CategoricallyRightInvertible.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class IsCatInv {A : Type} {has_hom : HasHom A}
  {has_eq_rel : forall x y : A, HasEqRel (x ~> y)}
  (has_comp : HasComp hom) (has_idt : HasIdt hom)
  (has_inv : HasInv hom) : Prop := {
  comp_idt_inv_is_l_cat_inv :> IsCatLInv comp idt inv;
  comp_idt_inv_is_r_cat_inv :> IsCatRInv comp idt inv;
}.
