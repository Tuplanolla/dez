(* bad *)
From Maniunfold.Has Require Export
  OneSortedBinaryOperation OneSortedNullaryOperation OneSortedUnaryOperation
  TwoSortedLeftAction TwoSortedLeftTorsion.
From Maniunfold.Is Require Export
  OneSortedGroup TwoSortedLeftGroupAction TwoSortedLeftUnique.

Class IsLGrpTor (A B : Type)
  `(HasBinOp A) `(HasNullOp A)
  `(HasUnOp A) `(HasLAct A B)
  `(HasLTor A B) : Prop := {
  A_B_bin_op_null_op_un_op_l_act_is_l_grp_act :>
    IsLGrpAct bin_op null_op un_op (l_act (A := A) (B := B));
  A_B_l_act_l_tor_l_uniq :> IsLUniq l_act l_tor;
}.
