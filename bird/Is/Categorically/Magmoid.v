From Maniunfold.Has Require Export
  Morphism EquivalenceRelation Composition.
From Maniunfold.Is Require Export
  Equivalence Proper.
From Maniunfold.ShouldHave Require Import
  CategoricalNotations.

Class IsMagd {A : Type} {has_hom : HasHom A}
  {has_eq_rel : forall x y : A, HasEqRel (x ~> y)}
  (has_comp : HasComp hom) : Prop := {
  eq_rel_is_eq :> forall x y : A, IsEq (A := x ~> y) eq_rel;
  comp_is_proper :> forall x y z : A,
    IsProper (eq_rel ==> eq_rel ==> eq_rel) (comp x y z);
}.
