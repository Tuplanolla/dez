(* bad *)
From Coq Require Import
  Lists.List Logic.ProofIrrelevance NArith.NArith ZArith.ZArith.
From DEZ.Has Require Export
  Enumerations Sizes Operations ArithmeticOperations.
From DEZ.Is Require Export
  Finite Isomorphic Monoid.

Definition is_left (A B : Prop) (s : sumbool A B) : bool :=
  if s then true else false.

(** Here is some crap. *)

Local Open Scope N_scope.

Import ListNotations.

Global Instance bool_has_enum : HasEnum bool := [false; true].

Global Instance bool_is_b_fin : IsBFin (A := bool) _=_.
Proof.
  exists (enum bool). split.
  - intros [].
    + right. left. reflexivity.
    + left. reflexivity.
  - apply IsNoDup_cons.
    + intros H. inversion H as [? ? K | ? ? K].
      * inversion K.
      * inversion K.
    + apply IsNoDup_cons.
      * intros H. inversion H.
      * apply IsNoDup_nil. Qed.

Global Instance bool_has_size : HasSize bool := 2.

Definition bool_has_iso :
  (bool -> {n : N | n < size bool}) * ({n : N | n < size bool} -> bool).
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
  IsIso _=_ _=_ (fst bool_has_iso) (snd bool_has_iso).
Proof.
  split; try typeclasses eauto.
  - intros [].
    + cbn. reflexivity.
    + cbn. reflexivity.
  - intros [[| p] H].
    + cbn. f_equal. apply proof_irrelevance.
    + cbn. destruct p as [| q _] using Pos.peano_ind.
      * f_equal. apply proof_irrelevance.
      * (** This mess eventually leads to a contradiction. *)
        pose proof H as F.
        cbv [size bool_has_size] in F.
        rewrite <- N.succ_pos_pred in F.
        rewrite Pos.pred_N_succ in F.
        rewrite N.two_succ in F.
        rewrite <- N.succ_lt_mono in F.
        rewrite N.lt_1_r in F.
        inversion F. Qed.
