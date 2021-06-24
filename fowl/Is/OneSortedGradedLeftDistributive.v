(* bad *)
From Maniunfold.Has Require Export
  BinaryOperation Addition OneSortedGradedMultiplication.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations OneSortedGradedArithmeticNotations.

Class IsGrdDistrL (A : Type) (P : A -> Type)
  `(HasBinOp A)
  `(forall i : A, HasAdd (P i))
  `(HasGrdMul A P) : Prop :=
  grd_distr_l : forall (i j : A) (x : P i) (y z : P j),
    x * (y + z)%ring = ((x * y)%grd_ring + (x * z)%grd_ring)%ring.
