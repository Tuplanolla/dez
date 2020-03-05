From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit UnaryOperation
  LeftAction LeftTorsion.
From Maniunfold.Is Require Export
  Group LeftGroupAction LeftCompatible.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

(** TODO Why group and not something less?
    Also, what should we call the [uniqueness_property_thing]? *)

Class IsLGrpTor {A B : Type}
  {A_has_eq_rel : HasEqRel A} {B_has_eq_rel : HasEqRel B}
  (has_bin_op : HasBinOp A) (has_un : HasUn A) (has_un_op : HasUnOp A)
  (has_l_act : HasLAct A B) (has_l_tor : HasLTor A B) : Prop := {
  bin_op_un_un_op_l_act_is_l_grp_act :> IsLGrpAct bin_op un un_op l_act;
  uniqueness_property_thing : forall x y : B, (y L- x) L+ x == y;
}.
