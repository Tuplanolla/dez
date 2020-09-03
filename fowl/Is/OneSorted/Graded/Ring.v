From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.Addition OneSorted.Zero OneSorted.Negation
  OneSorted.Graded.Multiplication OneSorted.Graded.One.
From Maniunfold.Is Require Export
  OneSorted.AbelianGroup OneSorted.Graded.Distributive OneSorted.Graded.Monoid.

(** Graded noncommutative ring.
    The grading is carried by [A] and the ring by [P].
    See [Is.OneSorted.Ring]. *)

Class IsGrdRing {A : Type} (P : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_add : forall i : A, HasAdd (P i))
  (P_has_zero : forall i : A, HasZero (P i))
  (P_has_neg : forall i : A, HasNeg (P i))
  (P_has_grd_mul : HasGrdMul P) (P_has_grd_one : HasGrdOne P) : Prop := {
  P_add_zero_neg_is_ab_grp :> forall i : A,
    IsAbGrp (P i) (P_has_add i) (P_has_zero i) (P_has_neg i);
  P_add_grd_mul_is_grd_distr :> IsGrdDistr P P_has_add grd_mul;
  P_grd_mul_grd_one_is_grd_mon :> IsGrdMon P grd_mul grd_one;
}.