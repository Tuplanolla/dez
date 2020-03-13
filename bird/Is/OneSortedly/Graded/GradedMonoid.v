From Coq Require Logic. Import Logic.EqNotations.
From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit.
From Maniunfold.Is Require Export
  Monoid.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations.
From Maniunfold.ShouldOffer Require Import
  MoreAdditiveNotations.

Class IsGrdMon {A : Type} {P : A -> Type}
  (A_has_bin_op : HasBinOp A) (A_has_un : HasUn A)
  (has_grd_bin_op : HasGrdBinOp A P) (has_grd_un : HasGrdUn A P) : Prop := {
  bin_op_un_is_mon :> IsMon (A := A) bin_op un;
  (** TODO Uninline the following. *)
  grd_assoc : forall (i j k : A) (x : P i) (y : P j) (z : P k),
    rew assoc i j k in (x G+ (y G+ z)) = (x G+ y) G+ z;
  grd_l_unl : forall (i : A) (x : P i),
    rew l_unl i in (G0 G+ x) = x;
  grd_r_unl : forall (i : A) (x : P i),
    rew r_unl i in (x G+ G0) = x;
}.
