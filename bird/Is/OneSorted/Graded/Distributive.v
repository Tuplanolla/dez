(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.Addition OneSorted.Graded.Multiplication.
From Maniunfold.Is Require Export
  OneSorted.Graded.LeftDistributive OneSorted.Graded.RightDistributive.

Class IsGrdDistr {A : Type} {P : A -> Type}
  {A_has_bin_op : HasBinOp A} (P_has_add : forall i : A, HasAdd (P i))
  (P_has_grd_mul : HasGrdMul P) : Prop := {
  add_grd_mul_is_grd_l_distr :> IsGrdLDistr P_has_add grd_mul;
  add_grd_mul_is_grd_r_distr :> IsGrdRDistr P_has_add grd_mul;
}.
