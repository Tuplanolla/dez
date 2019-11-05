From Maniunfold.Has Require Export
  EquivalenceRelation Composition.
From Maniunfold.Is Require Export
  Proper Setoid Associative.

Class IsSemicategory {A : Type}
  {has_arrow : HasArrow A} {has_eqv : forall x y : A, HasEqv (arrow x y)}
  (has_comp : HasComp arrow) : Prop := {
  eqv_is_setoidoid :> forall x y : A, IsSetoid (A := arrow x y) eqv;
  comp_is_proper :> forall x y z : A,
    IsProper (eqv ==> eqv ==> eqv) (comp x y z);
  (* comp_is_associative :> forall x y z : A, IsAssociative (comp x y z); *)
}.
