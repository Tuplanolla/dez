From Maniunfold.Has Require Export
  BinaryOperation Unit GradedBinaryOperation GradedUnit.
From Maniunfold.Is Require Export
  GradedLeftModule AbelianGroup.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations ArithmeticNotations.

(** TODO Do we really need commutativity and
    all these acrobatics on the index type? *)

Section Context.

Context {A : Type} `{is_mon : IsMon A} {is_comm : IsComm bin_op}.

Import AdditiveNotations.

Lemma swappy : forall i j k : A,
  j + (i + k) = i + (j + k).
Proof.
  intros i j k.
  rewrite (assoc j i k).
  rewrite (comm j i).
  rewrite <- (assoc i j k).
  reflexivity. Qed.

End Context.

Class IsGrdLAlg {A : Type} {P Q : A -> Type}
  (A_has_bin_op : HasBinOp A) (A_has_un : HasUn A) (A_has_un_op : HasUnOp A)
  (P_has_add : forall i : A, HasAdd (P i))
  (P_has_zero : forall i : A, HasZero (P i))
  (P_has_neg : forall i : A, HasNeg (P i))
  (P_has_grd_mul : HasGrdMul P) (P_has_grd_one : HasGrdOne P)
  (Q_has_add : forall i : A, HasAdd (Q i))
  (Q_has_zero : forall i : A, HasZero (Q i))
  (Q_has_neg : forall i : A, HasNeg (Q i))
  (Q_has_mul : forall i : A, HasMul (Q i))
  (P_Q_has_grd_l_act : HasGrdLAct P Q) : Prop := {
  this_is_grd_l_mod :>
    IsGrdLMod (P := P) (Q := Q)
    bin_op un un_op P_has_add P_has_zero P_has_neg
    grd_mul grd_one Q_has_add Q_has_zero Q_has_neg
    grd_l_act;
  (* z * (x + y) = z * x + z * y *)
  (* (x + y) * z = x * z + y * z *)
  the_l_distr : forall (i : A) (x y z : Q i),
    z * (x + y) = z * x + z * y;
  the_r_distr : forall (i : A) (x y z : Q i),
    (x + y) * z = x * z + y * z;
  the_weird_comm :> IsComm bin_op;
  (* a * (x * y) = (a * x) * y *)
  (* the_l_wtf : forall (i j k : A) (a : P i) (x : Q j) (y : Q k),
    rew [Q] assoc i j k in (a GL* (x G* y)) = (a GL* x) G* y;
  (* x * (b * y) = b * (x * y) *)
  the_r_wtf : forall (i j k : A) (a : P i) (x : Q j) (y : Q k),
    rew [Q] swappy i j k in (x G* (a GL* y)) = a GL* (x G* y); *)
}.

Section Context.

Context {A : Type} {P Q : A -> Type} `{is_grd_l_alg : IsGrdLAlg A P Q}.

Goal forall (i j k : A) (a : P i) (x : Q j) (y : Q k), True.
Proof.
  intros.
  eset (L := a GL* (x G* y)).
  eset (R := (a GL* x) G* y).
  eset (E := rew assoc i j k in L = R). Restart.
  intros.
  eset (L := x G* (a GL* y)).
  eset (R := a GL* (x G* y)).
  eset (L' := rew swappy i j k in L).
  eset (E := L' = R). Abort.

(** Why is this suddenly fine? *)

End Context.
