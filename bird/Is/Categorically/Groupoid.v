From Maniunfold.Has.Categorical Require Export
  Morphism Composition Identity Inverse.
From Maniunfold.Is.Categorically Require Export
  Category Invertible Involutive.
From Maniunfold.ShouldHave.Categorical Require Import
  Notations.

Class IsGrpd {A : Type} {has_hom : HasHom A}
  (has_comp : HasComp hom) (has_idt : HasIdt hom)
  (has_inv : HasInv hom) : Prop := {
  comp_idt_is_cat :> IsCat comp idt;
  comp_idt_inv_is_cat_inv :> IsCatInv comp idt inv;
}.

Section Context.

Context {A : Type} `{is_grpd : IsGrpd A}.

Theorem inv_cat_invol : forall {x y : A} (f : x --> y),
  (f ^-1) ^-1 = f.
Proof.
  intros x y f.
  rewrite <- (cat_r_unl ((f ^-1) ^-1)).
  rewrite <- (cat_l_inv f).
  rewrite (cat_assoc ((f ^-1) ^-1) (f ^-1) f).
  rewrite (cat_l_inv (f ^-1)).
  rewrite (cat_l_unl f).
  reflexivity. Qed.

Global Instance inv_is_cat_invol : IsCatInvol inv.
Proof. intros x y f. apply inv_cat_invol. Qed.

End Context.
