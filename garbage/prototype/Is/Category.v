From DEZ.Has Require Export
  Arrow Composition Identity.
From DEZ.Is Require Export
  Semicategory Biidentifiable.

Class IsCategory {A : Type}
  {has_arrow : HasArrow A} {has_eqv : forall x y : A, HasEqv (arrow x y)}
  (has_comp : HasComp arrow) (has_iden : HasIden arrow) : Prop := {
  comp_is_semicategory :> IsSemicategory comp;
  (* opr_idn_is_identifiable :> forall x y : A, IsBiidentifiable comp iden; *)
}.
