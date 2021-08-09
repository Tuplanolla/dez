From DEZ.Has Require Export
  Morphism IdentityMorphism InverseMorphism ComposedMorphism.
From DEZ.ShouldHave Require Import
  CategoricalNotations.

Class IsCatInvL (A : Type) (HC : HasHom A)
  (Hx : HasIdHom _-->_) (Hf : HasInvHom _-->_)
  (Hk : HasCompHom _-->_) : Prop :=
  cat_inv_l (x y : A) (f : x --> y) : f o f ^-1 = id.

Class IsCatInvR (A : Type) (HC : HasHom A)
  (Hx : HasIdHom _-->_) (Hf : HasInvHom _-->_)
  (Hk : HasCompHom _-->_) : Prop :=
  cat_inv_r (x y : A) (f : x --> y) : f ^-1 o f = id.

Class IsCatInvLR (A : Type) (HC : HasHom A)
  (Hx : HasIdHom _-->_) (Hf : HasInvHom _-->_)
  (Hk : HasCompHom _-->_) : Prop := {
  is_cat_inv_l :> IsCatInvL Hx Hf Hk;
  is_cat_inv_r :> IsCatInvR Hx Hf Hk;
}.
