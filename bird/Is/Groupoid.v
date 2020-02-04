From Maniunfold.Has Require Export
  Morphism EquivalenceRelation Composition Identity Inverse.
From Maniunfold.Is Require Export
  Category CategoricallyInvertible Involutive.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations CategoricalNotations.
From Maniunfold.ShouldOffer Require Import
  MoreCategoricalNotations.

Class IsGrpd {A : Type} {has_hom : HasHom A}
  {has_eq_rel : forall x y : A, HasEqRel (x ~> y)}
  (has_comp : HasComp hom) (has_idt : HasIdt hom)
  (has_inv : HasInv hom) : Prop := {
  comp_is_cat :> IsCat comp idt;
  comp_idt_inv_is_cat_inv :> IsCatInv comp idt inv;
}.

Section Context.

Context {A : Type} `{is_grpd : IsGrpd A}.

Theorem inv_invol : forall {x y : A} (f : x ~> y),
  f ^-1 ^-1 == f.
Proof.
  intros x y f.
  rewrite <- (cat_r_unl (f ^-1 ^-1)).
  rewrite <- (cat_l_inv f).
  rewrite (cat_assoc (f ^-1 ^-1) (f ^-1) f).
  rewrite (cat_l_inv (f ^-1)).
  rewrite (cat_l_unl f).
  reflexivity. Qed.

Fail Global Instance inv_is_invol : forall x y : A, IsInvol (inv x y).

End Context.
