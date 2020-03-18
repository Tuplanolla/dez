From Maniunfold.Has Require Export
  BinaryOperation NullaryOperation
  Graded.BinaryOperation Graded.NullaryOperation
  Graded.Multiplication Graded.One.
From Maniunfold.Is Require Export
  GradedMonoid AbelianGroup.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations OneSorted.AdditiveNotations
  OneSorted.Graded.MultiplicativeNotations.

Class IsGrdRing {A : Type} {P : A -> Type}
  (A_has_bin_op : HasBinOp A) (A_has_un : HasNullOp A)
  (P_has_add : forall i : A, HasAdd (P i))
  (P_has_zero : forall i : A, HasZero (P i))
  (P_has_neg : forall i : A, HasNeg (P i))
  (P_has_grd_mul : HasGrdMul P) (P_has_grd_one : HasGrdOne P) : Prop := {
  bin_op_null_op_grd_mul_grd_one_is_grd_mon :> IsGrdMon bin_op null_op grd_mul grd_one;
  add_zero_neg_is_ab_grp :> forall i : A, IsAbGrp (A := P i) add zero neg;
  (** TODO NullOpinline the following, use operational notations and
      check whether to unify the index types (guess: no). *)
  (* add_grd_mul_is_distr :> IsDistrFiber add grd_mul; *)
  grd_l_distr : forall (i j : A) (x : P i) (y z : P j),
    x G* (y + z) = x G* y + x G* z;
  grd_r_distr : forall (i j : A) (x y : P i) (z : P j),
    (x + y) G* z = x G* z + y G* z;
}.
