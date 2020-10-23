From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition Categorical.Identity
  Categorical.Inverse.
From Maniunfold.Is Require Export
  Categorical.LeftInvertible Categorical.RightInvertible.

Class IsCatInv (A : Type) `{HasHom A}
  `(!HasComp hom) `(!HasIdt hom)
  `(!HasInv hom) : Prop := {
  A_comp_idt_inv_is_cat_l_inv :> IsCatLInv comp idt inv;
  A_comp_idt_inv_is_cat_r_inv :> IsCatRInv comp idt inv;
}.
