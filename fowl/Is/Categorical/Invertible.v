From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition Categorical.Identity
  Categorical.Inverse.
From Maniunfold.Is Require Export
  Categorical.LeftInvertible Categorical.RightInvertible.

Class IsCatInv (A : Type)
  `(HasHom A) `(!HasComp hom) `(!HasIdt hom) `(!HasInv hom) : Prop := {
  hom_comp_idt_inv_is_cat_l_inv :> IsCatLInv hom comp idt inv;
  hom_comp_idt_inv_is_cat_r_inv :> IsCatRInv hom comp idt inv;
}.
