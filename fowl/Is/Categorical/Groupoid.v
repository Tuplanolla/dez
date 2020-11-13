From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition Categorical.Identity
  Categorical.Inverse.
From Maniunfold.Is Require Export
  Categorical.Category Categorical.Invertible Categorical.Involutive.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

Class IsGrpd (A : Type)
  `(HasHom A) `(!HasComp hom) `(!HasIdt hom) `(!HasInv hom) : Prop := {
  hom_comp_idn_is_cat :> IsCat hom comp idn;
  hom_comp_idn_inv_is_cat_inv :> IsCatInv hom comp idn inv;
}.

Section Context.

Context (A : Type) `{IsGrpd A}.

Theorem hom_inv_cat_invol (x y : A) (f : x --> y) : (f ^-1) ^-1 = f.
Proof.
  rewrite <- (cat_r_unl _ _ ((f ^-1) ^-1)).
  rewrite <- (cat_l_inv _ _ f).
  rewrite (cat_assoc _ _ _ _ ((f ^-1) ^-1) (f ^-1) f).
  rewrite (cat_l_inv _ _ (f ^-1)).
  rewrite (cat_l_unl _ _ f).
  reflexivity. Qed.

Global Instance hom_inv_is_cat_invol : IsCatInvol hom inv.
Proof. exact @hom_inv_cat_invol. Qed.

End Context.
