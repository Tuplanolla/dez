From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition Categorical.Identity
  Categorical.Inverse.
From Maniunfold.Is Require Export
  Categorical.LeftInvertible Categorical.RightInvertible.

Class IsCatInv (A : Type)
  `(HasHom A) `(!HasComp hom) `(!HasIdt hom) `(!HasInv hom) : Prop := {
  comp_idn_inv_is_cat_l_inv :> IsCatLInv comp idn inv;
  comp_idn_inv_is_cat_r_inv :> IsCatRInv comp idn inv;
}.
