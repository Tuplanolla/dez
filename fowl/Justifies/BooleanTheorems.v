(* bad *)
From Coq Require Import
  Lists.List Logic.ProofIrrelevance NArith.NArith ZArith.ZArith.
From DEZ.Has Require Export
  Zero Negation Addition One Multiplication
  NullaryOperation UnaryOperation BinaryOperation
  OneSortedEnumeration OneSortedCardinality.
From DEZ.Is Require Export
  OneSortedFinite Isomorphism Monoid.

Definition is_left (A B : Prop) (s : sumbool A B) : bool :=
  if s then true else false.

(** Here is some crap. *)

Local Open Scope N_scope.

Import ListNotations.

Global Instance bool_has_enum : HasEnum bool := [false; true].

Global Instance bool_is_b_fin : IsBFin enum.
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

Definition bool_has_iso :
  (bool -> {n : N | n < card bool}) * ({n : N | n < card bool} -> bool).
Proof.
  split.
  - intros [].
    (** We map [true] into [1] and [false] into [0]. *)
    + exists N.one. apply N.lt_1_2.
    + exists N.zero. apply N.lt_0_2.
  - intros [[| p] H].
    (** We thus decree that [false] is less than [true]. *)
    + apply false.
    + apply true. Defined.

Global Instance bool_is_fin :
  IsFin (card bool) (fst bool_has_iso) (snd bool_has_iso).
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

Local Instance bool_bin_op_is_assoc : IsAssoc _=_ orb.
Proof.
  intros x y z. all: cbn; repeat match goal with
  | x : bool |- _ => destruct x
  | x : unit |- _ => destruct x
  end; try reflexivity. Defined.

Local Instance bool_bin_op_is_unl_l : IsUnlL _=_ null_op (bin_op (A := bool)).
Proof.
  intros x. all: cbn; repeat match goal with
  | x : bool |- _ => destruct x
  | x : unit |- _ => destruct x
  end; try reflexivity. Defined.

Local Instance bool_bin_op_is_unl_r : IsUnlR _=_ null_op (bin_op (A := bool)).
Proof.
  intros x. all: cbn; repeat match goal with
  | x : bool |- _ => destruct x
  | x : unit |- _ => destruct x
  end; try reflexivity. Defined.

End Stuff.
