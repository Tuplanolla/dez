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

Local Open Scope grd_r_mod_scope.

Class IsGrdRCompat {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_grd_mul : HasGrdMul P)
  (P_Q_has_grd_r_act : HasGrdRAct P Q) : Prop := {
  A_bin_op_is_assoc :> IsAssoc A bin_op;
  grd_r_compat : forall {i j k : A} (x : Q i) (a : P j) (b : P k),
    rew assoc i j k in (x * (a * b)) = (x * a) * b;
}.
