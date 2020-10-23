From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition Categorical.Identity
  Categorical.Inverse.
From Maniunfold.Is Require Export
  Categorical.LeftInvertible Categorical.RightInvertible.

Class IsCatInv (A : Type) `{HasHom A}
  `(!HasComp A hom) `(!HasIdt A hom)
  `(!HasInv A hom) : Prop := {
  A_comp_idt_inv_is_cat_l_inv :> IsCatLInv A comp idt inv;
  A_comp_idt_inv_is_cat_r_inv :> IsCatRInv A comp idt inv;
}.
