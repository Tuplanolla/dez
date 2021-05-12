From Maniunfold.Has Require Export
  OneSortedBinaryOperation OneSortedNullaryOperation
  OneSortedAddition OneSortedZero OneSortedNegation
  OneSortedGradedMultiplication OneSortedGradedOne.
From Maniunfold.Is Require Export
  OneSortedAbelianGroup OneSortedGradedDistributive OneSortedGradedMonoid.

(** Graded noncommutative ring.
    The grading is carried by [A] and the ring by [P].
    See [Is.OneSortedRing]. *)

Class IsGrdRing (A : Type) (P : A -> Type)
  `(HasBinOp A) `(HasNullOp A)
  `(P_has_add : forall i : A, HasAdd (P i))
  `(P_has_zero : forall i : A, HasZero (P i))
  `(P_has_neg : forall i : A, HasNeg (P i))
  `(!HasGrdMul P bin_op) `(!HasGrdOne P null_op) : Prop := {
  add_zero_neg_is_ab_grp :> forall i : A,
    IsAbGrp (P_has_add i) (P_has_zero i) (P_has_neg i);
  add_grd_mul_is_grd_distr :> IsGrdDistr bin_op P_has_add grd_mul;
  grd_mul_grd_one_is_grd_mon :> IsGrdMon bin_op null_op grd_mul grd_one;
}.
