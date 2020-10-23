(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  Graded.BinaryOperation Graded.NullaryOperation TwoSorted.Graded.LeftAction.
From Maniunfold.Is Require Export
  Graded.Ring AbelianGroup.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations OneSorted.AdditiveNotations
  OneSorted.Graded.MultiplicativeNotations
  TwoSorted.Graded.MultiplicativeNotations.

Local Open Scope grd_l_mod_scope.

Class IsGrdLCompat {A : Type} (P Q : A -> Type)
  `{HasBinOp A} `{HasNullOp A}
  `(!@HasGrdMul A P bin_op)
  `(!@HasGrdLAct A P Q bin_op) : Prop := {
  A_bin_op_is_assoc :> IsAssoc bin_op;
  grd_l_compat : forall {i j k : A} (a : P i) (b : P j) (x : Q k),
    rew assoc i j k in (a * (b * x)) = (a * b) * x;
}.
