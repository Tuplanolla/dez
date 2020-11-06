From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition Categorical.Identity
  Categorical.Inverse.
From Maniunfold.Is Require Export
  Categorical.Category Categorical.Invertible Categorical.Involutive.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

Class IsGrpd (A : Type)
  `(HasHom A) `(!HasComp hom) `(!HasIdt hom) `(!HasInv hom) : Prop := {
  hom_comp_idt_is_cat :> IsCat hom comp idt;
  hom_comp_idt_inv_is_cat_inv :> IsCatInv hom comp idt inv;
}.

Section Context.

Context (A : Type) `(IsGrpd A).

Global Instance inv_is_cat_invol : IsCatInvol hom inv.
Proof.
  intros x y f.
  rewrite <- (cat_r_unl ((f ^-1) ^-1)).
  rewrite <- (cat_l_inv f).
  rewrite (cat_assoc ((f ^-1) ^-1) (f ^-1) f).
  rewrite (cat_l_inv (f ^-1)).
  rewrite (cat_l_unl f).
  reflexivity. Defined.

End Context.
