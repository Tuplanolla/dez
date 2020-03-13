From Maniunfold.Has Require Export
  BinaryOperation Unit GradedBinaryOperation GradedUnit.
From Maniunfold.Is Require Export
  GradedMonoid AbelianGroup.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations AdditiveNotations.
From Maniunfold.ShouldOffer Require Import
  MoreAdditiveNotations.

(** TODO Move these once the notations are settled. *)

Class HasGrdMul {A : Type} (P : A -> Type) {has_bin_op : HasBinOp A} : Type :=
  grd_mul : forall i j : A, P i -> P j -> P (i + j).

Typeclasses Transparent HasGrdMul.

Class HasGrdOne {A : Type} (P : A -> Type) {has_un : HasUn A} : Type :=
  grd_one : P 0.

Typeclasses Transparent HasGrdOne.

Reserved Notation "x 'G*' y" (at level 40, left associativity).
Reserved Notation "'G1'" (at level 0, no associativity).

Notation "x 'G*' y" := (grd_mul _ _ x y) : algebra_scope.
Notation "'G1'" := grd_one : algebra_scope.

Class IsGrdRing {A : Type} {P : A -> Type}
  (A_has_bin_op : HasBinOp A) (A_has_un : HasUn A)
  (P_has_add : forall i : A, HasAdd (P i))
  (P_has_zero : forall i : A, HasZero (P i))
  (P_has_neg : forall i : A, HasNeg (P i))
  (P_has_grd_mul : HasGrdMul P) (P_has_grd_one : HasGrdOne P) : Prop := {
  bin_op_un_grd_mul_grd_one_is_grd_mon :> IsGrdMon bin_op un grd_mul grd_one;
  add_zero_neg_is_ab_grp :> forall i : A, IsAbGrp (A := P i) add zero neg;
  (** TODO Uninline the following, use operational notations and
      check whether to unify the index types (guess: no). *)
  (* add_grd_mul_is_distr :> IsDistrFiber add grd_mul; *)
  grd_l_distr : forall (i j : A) (x : P i) (y z : P j),
    x G* (y + z) = x G* y + x G* z;
  grd_r_distr : forall (i j : A) (x y : P i) (z : P j),
    (x + y) G* z = x G* z + y G* z;
}.
