From Maniunfold.Has Require Export
  Categorical.Morphism Categorical.Composition.
From Maniunfold.ShouldHave Require Import
  Categorical.Notations.

(** TODO We can only mark the endpoint objects implicit
    if the implementation of `hom` actually uses both of its arguments;
    otherwise type inference fails (by strict ia violation).
    Investigate. *)

Class IsCatAssoc (A : Type) `(HasHom A) `(!HasComp hom) : Prop :=
  cat_assoc : forall {x y z w : A} (f : x --> y) (g : y --> z) (h : z --> w),
    (h o g) o f = h o (g o f).
