From Coq Require Import
  Lists.List Logic.ProofIrrelevance NArith.NArith.
From Maniunfold.Has Require Export
  OneSorted.Enumeration OneSorted.Cardinality TwoSorted.Isomorphism.
From Maniunfold.Is Require Export
  OneSorted.Finite TwoSorted.Isomorphism.
From Maniunfold.Offers Require Export
  TwoSorted.IsomorphismMappings.

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
      * apply NoDup_nil. Qed.

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
        inversion F. Qed.
