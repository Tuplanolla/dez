From Maniunfold.Has Require Export
  HigherEquivalenceRelation Composition Identity.
From Maniunfold.Is Require Export
  Semicategory Biidentifiable.

Class IsCategory {A : Type}
  {has_arrow : HasArrow A} {has_hieqv : HasHiEqv arrow}
  (has_comp : HasComp arrow) (has_iden : HasIden arrow) : Prop := {
  comp_is_semicategory :> IsSemicategory has_comp;
  (* opr_idn_is_identifiable :> IsBiidentifiable opr idn; *)
}.
