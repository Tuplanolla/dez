(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.Addition OneSorted.Graded.Multiplication.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations OneSorted.Graded.ArithmeticNotations.

Class IsGrdRDistr {A : Type} {P : A -> Type}
  {A_has_bin_op : HasBinOp A} (P_has_add : forall i : A, HasAdd (P i))
  (P_has_grd_mul : HasGrdMul P) : Prop :=
  grd_r_distr : forall {i j : A} (x y : P i) (z : P j),
    (x + y)%ring * z = ((x * z)%grd_ring + (y * z)%grd_ring)%ring.
