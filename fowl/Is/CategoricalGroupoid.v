From Maniunfold.Has Require Export
  CategoricalMorphism CategoricalComposition CategoricalIdentity
  CategoricalInverse.
From Maniunfold.Is Require Export
  CategoricalCategory CategoricalInvertible CategoricalInvolutive.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class IsGrpd (A : Type)
  `(HasHom A) `(!HasComp hom) `(!HasIdt hom) `(!HasInv hom) : Prop := {
  comp_idn_is_cat :> IsCat comp idn;
  comp_idn_inv_is_cat_inv :> IsCatInv comp idn inv;
}.

Section Context.

Context (A : Type) `{IsGrpd A}.

Theorem inv_cat_invol (x y : A) (f : x --> y) : (f ^-1) ^-1 = f.
Proof.
  rewrite <- (cat_r_unl _ _ ((f ^-1) ^-1)).
  rewrite <- (cat_l_inv _ _ f).
  rewrite (cat_assoc _ _ _ _ ((f ^-1) ^-1) (f ^-1) f).
  rewrite (cat_l_inv _ _ (f ^-1)).
  rewrite (cat_l_unl _ _ f).
  reflexivity. Qed.

Global Instance inv_is_cat_invol : IsCatInvol inv.
Proof. exact @inv_cat_invol. Qed.

End Context.
