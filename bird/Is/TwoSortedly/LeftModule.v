From Maniunfold.Has Require Export
  EquivalenceRelation Addition Zero Negation Multiplication One
  BinaryOperation Unit UnaryOperation LeftAction.
From Maniunfold.Is Require Export
  OneSortedly.Ring TwoSortedly.RightDistributive TwoSortedly.LeftCompatible
  OneSortedly.AbelianGroup TwoSortedly.LeftDistributive TwoSortedly.LeftUnital.

Class IsLMod {A B : Type}
  {A_has_eq_rel : HasEqRel A} {B_has_eq_rel : HasEqRel B}
  (A_has_add : HasAdd A) (A_has_zero : HasZero A) (A_has_neg : HasNeg A)
  (A_has_mul : HasMul A) (A_has_one : HasOne A)
  (B_has_bin_op : HasBinOp B) (B_has_un : HasUn B) (B_has_un_op : HasUnOp B)
  (has_l_act : HasLAct A B) : Prop := {
  add_zero_neg_mul_one_is_ring :> IsRing (A := A) add zero neg mul one;
  add_l_act_is_two_r_distr :> IsTwoRDistr (A := A) (B := B) add bin_op l_act;
  mul_l_act_is_l_compat :> IsLCompat (A := A) (B := B) mul l_act;
  bin_op_un_un_op_is_ab_grp :> IsAbGrp (A := B) bin_op un un_op;
  bin_op_l_act_is_two_l_distr :> IsTwoLDistr (A := A) (B := B) bin_op l_act;
  un_l_act_is_two_l_unl :> IsTwoLUnl (A := A) (B := B) un l_act;
}.
