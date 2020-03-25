From Maniunfold.Has Require Export
  OneSorted.UnaryOperation OneSorted.Addition TwoSorted.LeftAction.
From Maniunfold.Is Require Import
  OneSorted.UnaryDistributive TwoSorted.RightBinaryCommutative.

Class IsLLin {A B : Type}
  (A_has_un_op : HasUnOp A) (A_has_add : HasAdd A)
  (A_B_has_l_act : HasLAct A B) : Prop := {
  (* f (x + y) = f (x) + f (y) *)
  wtf :> IsUnDistr add un_op;
  (* f (a L* x) = a L* f (x) *)
  wtfs :> IsTwoRBinComm un_op l_act;
}.
