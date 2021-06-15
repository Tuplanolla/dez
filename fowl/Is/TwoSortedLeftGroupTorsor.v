(* bad *)
From Maniunfold.Has Require Export
  BinaryOperation OneSortedNullaryOperation OneSortedUnaryOperation
  Action TwoSortedLeftTorsion.
From Maniunfold.Is Require Export
  OneSortedGroup TwoSortedLeftGroupAction TwoSortedLeftUnique.

Class IsLGrpTor (A B : Type)
  `(HasBinOp A) `(HasNullOp A)
  `(HasUnOp A) `(HasActL A B)
  `(HasLTor A B) : Prop := {
  A_B_bin_op_null_op_un_op_act_l_is_l_grp_act :>
    IsLGrpAct bin_op null_op un_op (act_l (A := A) (B := B));
  A_B_act_l_l_tor_l_uniq :> IsLUniq act_l l_tor;
}.
