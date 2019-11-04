From Maniunfold.Has Require Export
  HigherEquivalenceRelation Composition.
From Maniunfold.Is Require Export
  Proper Setoidoid Associative.

Class IsSemicategory {A : Type}
  {has_arrow : HasArrow A} {has_hieqv : HasHiEqv arrow}
  (has_comp : HasComp arrow) : Prop := {
  hieqv_is_setoidoid :> IsSetoidoid has_hieqv;
  (* comp_is_proper :> IsProper (hieqv ==> hieqv ==> hieqv) comp; *)
  (* comp_is_associative :> IsAssociative comp; *)
}.
