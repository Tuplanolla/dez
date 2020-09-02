From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition Categorical.Identity
  Categorical.Inverse.
From Maniunfold.Is Require Export
  Categorical.LeftInvertible Categorical.RightInvertible.

Class IsCatInv (A : Type) {A_has_hom : HasHom A}
  (A_hom_has_comp : HasComp A hom) (A_hom_has_idt : HasIdt A hom)
  (A_hom_has_inv : HasInv A hom) : Prop := {
  A_comp_idt_inv_is_cat_l_inv :> IsCatLInv A comp idt inv;
  A_comp_idt_inv_is_cat_r_inv :> IsCatRInv A comp idt inv;
}.
