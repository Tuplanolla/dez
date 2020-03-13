From Maniunfold.Has.OneSorted Require Export
  UnaryOperation.
From Maniunfold.ShouldHave.OneSorted Require Import
  AdditiveNotations.

Class IsInvol {A : Type} (has_un_op : HasUnOp A) : Prop :=
  invol : forall x : A, - (- x) = x.
