From Maniunfold.Has.Categorical Require Export
  Morphism Composition Identity Inverse.
From Maniunfold.Is.Categorically Require Export
  LeftInvertible RightInvertible.

Class IsCatInv {A : Type} {has_hom : HasHom A}
  (has_comp : HasComp hom) (has_idt : HasIdt hom)
  (has_inv : HasInv hom) : Prop := {
  comp_idt_inv_is_cat_l_inv :> IsCatLInv comp idt inv;
  comp_idt_inv_is_cat_r_inv :> IsCatRInv comp idt inv;
}.
