From Coq Require Logic. Import Logic.EqNotations.
From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit LeftAction.
From Maniunfold.Is Require Export
  Ring.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations AdditiveNotations.

(** TODO Move these. *)

Class HasGrdMul (A : Type) (P : A -> Type) {has_bin_op : HasBinOp A} : Type :=
  grd_mul : forall i j : A, P i -> P j -> P (i + j).

Typeclasses Transparent HasGrdMul.

Class HasGrdOne (A : Type) (P : A -> Type) {has_un : HasUn A} : Type :=
  grd_one : P 0.

Typeclasses Transparent HasGrdOne.

Notation "x '*' y" := (grd_mul _ _ x y) : algebra_scope.
Notation "'1'" := grd_one : algebra_scope.

Class IsGrdRingE {A : Type} {P : A -> Type}
  (A_has_bin_op : HasBinOp A) (A_has_un : HasUn A)
  (P_has_add : forall i : A, HasAdd (P i))
  (P_has_zero : forall i : A, HasZero (P i))
  (P_has_neg : forall i : A, HasNeg (P i))
  (has_grd_mul : HasGrdMul A P) (has_grd_one : HasGrdOne A P) : Prop := {
  bin_op_un_is_monE :> IsMonE (A := A) bin_op un;
  add_zero_neg_is_ab_grpE :> forall i : A, IsAbGrpE (A := P i) add zero neg;

  (** TODO Uninline the following, use operational notations and
      check whether to unify the index types. *)
  (* add_grd_mul_is_distr :> IsDistrFiber add grd_mul; *)

  grd_l_distr : forall (i j : A) (x : P i) (y : P j) (z : P j),
    grd_mul _ _ x (add y z) = add (grd_mul _ _ x y) (grd_mul _ _ x z);
  (* x * (y + z) = x * y + x * z; *)

  grd_r_distr : forall (i j : A) (x : P i) (y : P i) (z : P j),
    grd_mul _ _ (add x y) z = add (grd_mul _ _ x z) (grd_mul _ _ y z);
  (* (x + y) * z == x * z + y * z; *)

  (** TODO Do the same here. *)
  (* grd_mul_grd_one_is_mon :> IsMonFiber grd_mul grd_one; *)

  grd_assoc : forall (i j k : A) (x : P i) (y : P j) (z : P k),
    rew assocE i j k in
    grd_mul i (j + k) x (grd_mul j k y z) =
    grd_mul (i + j) k (grd_mul i j x y) z;
  (* x * (y * z) = (x * y) * z; *)

  grd_l_unl : forall (i : A) (x : P i),
    rew l_unlE i in grd_mul 0 i grd_one x = x;
  (* 1 * x = x; *)

  grd_r_unl : forall (i : A) (x : P i),
    rew r_unlE i in grd_mul i 0 x grd_one = x;
  (* x * 1 = x; *)
}.

Section Context.

Context {A : Type} {P : A -> Type} `{is_grd_ringE : IsGrdRingE A P}.

Check ?[IsDistrFiber] add grd_mul : Prop.
Check ?[IsMonFiber] grd_mul grd_one : Prop.

End Context.
