(* bad *)
From Maniunfold.Has Require Export
  OneSorted.BinaryOperation OneSorted.NullaryOperation
  OneSorted.Graded.BinaryOperation OneSorted.Graded.NullaryOperation
  TwoSorted.Graded.LeftAction TwoSorted.Graded.RightAction.
From Maniunfold.Is Require Export
  TwoSorted.Graded.Bimodule AbelianGroup.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations OneSorted.AdditiveNotations
  OneSorted.Graded.MultiplicativeNotations
  TwoSorted.Graded.MultiplicativeNotations.

(** TODO Do we really need commutativity and
    all these acrobatics on the index type?
    The answer is no and involves bimodules. *)

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

(** TODO There is some confusion about the operational requirements and
    appropriate use of commutativity... *)

Class IsGrdAlg' {A : Type} {P Q : A -> Type}
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_add : forall i : A, HasAdd (P i))
  (P_has_zero : forall i : A, HasZero (P i))
  (P_has_neg : forall i : A, HasNeg (P i))
  (P_has_grd_mul : HasGrdMul P) (P_has_grd_one : HasGrdOne P)
  (Q_has_add : forall i : A, HasAdd (Q i))
  (Q_has_zero : forall i : A, HasZero (Q i))
  (Q_has_neg : forall i : A, HasNeg (Q i))
  (** TODO ??? *) (Q_has_mul : forall i : A, HasMul (Q i))
  (Q_has_grd_mul : HasGrdMul Q)
  (P_Q_has_grd_l_act : HasGrdLAct P Q)
  (P_Q_has_grd_r_act : HasGrdRAct P Q) : Prop := {
  this_is_grd_l_mod :> IsGrdLMod P Q
    P_has_add P_has_zero P_has_neg
    grd_mul grd_one Q_has_add Q_has_zero Q_has_neg
    grd_l_act;
  (* z * (x + y) = z * x + z * y *)
  (* (x + y) * z = x * z + y * z *)
  the_l_distr : forall {i : A} (x y z : Q i),
    z * (x + y) = z * x + z * y;
  the_r_distr : forall {i : A} (x y z : Q i),
    (x + y) * z = x * z + y * z;
  the_weird_comm :> IsComm bin_op;
  (* a * (x * y) = (a * x) * y *)
  the_l_wtf : forall {i j k : A} (a : P i) (x : Q j) (y : Q k),
    rew [Q] assoc i j k in (a GL* (x G* y)) = (a GL* x) G* y;
  (* x * (b * y) = b * (x * y) *)
  the_r_wtf : forall {i j k : A} (a : P i) (x : Q j) (y : Q k),
    rew [Q] swappy i j k in (x G* (a GL* y)) = a GL* (x G* y);
}.

(** Worry not, just try again! *)

Fail Class IsGrdAlg {A : Type} (P Q : A -> Type)
  {A_has_bin_op : HasBinOp A} {A_has_null_op : HasNullOp A}
  (P_has_add : forall i : A, HasAdd (P i))
  (P_has_zero : forall i : A, HasZero (P i))
  (P_has_neg : forall i : A, HasNeg (P i))
  (P_has_grd_mul : HasGrdMul P) (P_has_grd_one : HasGrdOne P)
  (Q_has_add : forall i : A, HasAdd (Q i))
  (Q_has_zero : forall i : A, HasZero (Q i))
  (Q_has_neg : forall i : A, HasNeg (Q i))
  (** TODO Is this to be graded? *)
  (Q_has_grd_mul : HasGrdMul Q)
  (P_Q_has_grd_l_act : HasGrdLAct P Q)
  (P_Q_has_grd_r_act : HasGrdRAct P Q) : Prop := {
  add_zero_neg_grd_mul_grd_one_is_grd_ring :>
    IsGrdRing (P := P) P_has_add P_has_zero P_has_neg grd_mul grd_one;
  P_Q_add_zero_neg_grd_mul_grd_one_add_zero_neg_grd_l_act_grd_r_act_is_two_grd_bimod :>
    IsTwoGrdBimod P Q P_has_add P_has_zero P_has_neg grd_mul grd_one
    Q_has_add Q_has_zero Q_has_neg grd_l_act grd_r_act;
  (** TODO Need this first. *)
  P_Q_add_zero_neg_gdr_mul_gdr_one_add_zero_neg_WHAT_gdr_l_act_gdr_r_act_is_gdr_bilin_op :>
    IsGrdBilinOp P Q P_has_add P_has_zero P_has_neg grd_mul grd_one
    Q_has_add Q_has_zero Q_has_neg WHAT grd_l_act grd_r_act;
}.

Section Context.

Context {A : Type} {P Q : A -> Type} `{is_grd_alg : IsGrdAlg' A P Q}.

Local Set Warnings "-undo-batch-mode".

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

End Context.
