(* bad *)
From Coq Require Import
  Lists.List Logic.ProofIrrelevance NArith.NArith ZArith.ZArith.
From Maniunfold.Has Require Export
  OneSorted.Enumeration OneSorted.Cardinality TwoSorted.Isomorphism.
From Maniunfold.Is Require Export
  OneSorted.Finite TwoSorted.Isomorphism TwoSorted.Graded.Algebra.
From Maniunfold.Offers Require Export
  TwoSorted.IsomorphismMappings.

(** Here is some crap. *)

Local Open Scope N_scope.

Import ListNotations.

Global Instance bool_has_enum : HasEnum bool := [false; true].

Global Instance bool_is_b_fin : IsBFin bool.
Proof.
  split.
  - intros [].
    + right. left. reflexivity.
    + left. reflexivity.
  - apply NoDup_cons.
    + intros [H | H].
      * inversion H.
      * inversion H.
    + apply NoDup_cons.
      * intros H. inversion H.
      * apply NoDup_nil. Defined.

Global Instance bool_has_card : HasCard bool := 2.

Global Instance bool_has_iso : HasIso bool {n : N | n < card bool}.
Proof.
  split.
  - intros [].
    (** We map [true] into [1] and [false] into [0]. *)
    + exists 1. apply N.lt_1_2.
    + exists 0. apply N.lt_0_2.
  - intros [[| p] H].
    (** We thus decree that [false] is less than [true]. *)
    + apply false.
    + apply true. Defined.

Global Instance bool_is_fin : IsFin bool.
Proof.
  split.
  - intros [].
    + cbn. reflexivity.
    + cbn. reflexivity.
  - intros [[| p] H].
    + cbn. f_equal. apply proof_irrelevance.
    + cbn. destruct p as [| q _] using Pos.peano_ind.
      * f_equal. apply proof_irrelevance.
      * (** This mess eventually leads to a contradiction. *)
        pose proof H as F.
        cbv [card bool_has_card] in F.
        rewrite <- N.succ_pos_pred in F.
        rewrite Pos.pred_N_succ in F.
        rewrite N.two_succ in F.
        rewrite <- N.succ_lt_mono in F.
        rewrite N.lt_1_r in F.
        inversion F. Defined.

Section Stuff.

(** Let us set up a simple yet nontrivial graded ring,
    just to see what the dependent indexing gets us. *)

Local Open Scope Z_scope.

Local Instance bool_has_bin_op : HasBinOp bool := orb.

Local Instance bool_has_null_op : HasNullOp bool := false.

Local Instance Z_has_add : HasAdd Z := Z.add.

Local Instance Z_has_zero : HasZero Z := Z.zero.

Local Instance Z_has_neg : HasNeg Z := Z.opp.

Local Instance unit_has_add : HasAdd unit := fun x y : unit => tt.

Local Instance unit_has_zero : HasZero unit := tt.

Local Instance unit_has_neg : HasNeg unit := fun x : unit => tt.

Local Instance unit_Z_has_add (i : bool) :
  HasAdd (if i then unit else Z).
Proof. hnf. intros x y. destruct i. all: apply (add x y). Defined.

Local Instance unit_Z_has_zero (i : bool) :
  HasZero (if i then unit else Z).
Proof. hnf. destruct i. all: apply zero. Defined.

Local Instance unit_Z_has_neg (i : bool) :
  HasNeg (if i then unit else Z).
Proof. hnf. intros x. destruct i. all: apply (neg x). Defined.

Local Instance this_has_grd_mul :
  HasGrdMul (fun x : bool => if x then unit else Z).
Proof.
  hnf. intros i j x y. destruct i, j. all: cbv.
  - apply tt.
  - apply x.
  - apply y.
  - apply (x * y). Defined.

Local Instance this_has_grd_one :
  HasGrdOne (fun x : bool => if x then unit else Z).
Proof. hnf. apply 1. Defined.

Local Instance bool_bin_op_is_assoc : IsAssoc bool bin_op.
Proof.
  intros x y z. all: cbn; repeat match goal with
  | x : bool |- _ => destruct x
  | x : unit |- _ => destruct x
  end; try reflexivity. Defined.

Local Instance bool_bin_op_is_l_unl : IsLUnl bool bin_op null_op.
Proof.
  intros x. all: cbn; repeat match goal with
  | x : bool |- _ => destruct x
  | x : unit |- _ => destruct x
  end; try reflexivity. Defined.

Local Instance bool_bin_op_is_r_unl : IsRUnl bool bin_op null_op.
Proof.
  intros x. all: cbn; repeat match goal with
  | x : bool |- _ => destruct x
  | x : unit |- _ => destruct x
  end; try reflexivity. Defined.

(** TODO If we used [Qed] with these lemmas used in [rew],
    reduction would get stuck due to the lack of axiom K or
    its strict proposition equivalent. *)

Ltac smash := repeat match goal with
  | x : bool |- _ => destruct x
  | x : unit |- _ => destruct x
  end; try reflexivity.

Local Instance Z_bool_is_grd_ring :
  IsGrdRing (A := bool) (fun x : bool => if x then unit else Z)
  unit_Z_has_add unit_Z_has_zero unit_Z_has_neg grd_mul grd_one.
Proof.
  repeat split.
  1-6: shelve.
  - intros i j x y z.
    all: cbn; smash. apply Z.mul_add_distr_l.
  - intros i j x y z.
    all: cbn; smash. apply Z.mul_add_distr_r.
  - intros x y z. all: cbn; smash.
  - intros x. all: cbn; smash.
  - intros x y z. all: cbn; smash.
  - esplit.
    intros i j k x y z. all: cbn; smash. apply Z.mul_assoc.
  - esplit.
    intros i x. all: cbn -[Z.mul]; smash. apply Z.mul_1_l.
  - esplit.
    intros i x. all: cbn -[Z.mul]; smash. apply Z.mul_1_r. Abort.

End Stuff.
