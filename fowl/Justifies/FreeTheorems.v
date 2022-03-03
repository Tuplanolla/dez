(** * Free Structure *)

From Coq Require Import
  Extraction Lia Lists.List ZArith.ZArith.
From DEZ.Has Require Export
  Decisions Unsquashing.
From DEZ.Is Require Export
  Group Truncated.
From DEZ.Justifies Require Export
  BooleanTheorems (* ListTheorems *) ProductTheorems UnitTheorems ZTheorems.
From DEZ.Supports Require Import
  EquivalenceNotations AdditiveNotations.

#[local] Instance list_has_null_op (A : Type) : HasNullOp (list A) := nil.
#[local] Instance list_has_bin_op (A : Type) : HasBinOp (list A) := app.

#[local] Open Scope sig_scope.

Module Mess.

#[global] Instance prod_has_equiv_dec (A B : Type)
  (e : HasEqDec A) (f : HasEqDec B) : HasEqDec (A * B).
Proof.
  intros [x y] [z w]. destruct (e x z) as [a | a], (f y w) as [b | b].
  - left. congruence.
  - right. congruence.
  - right. congruence.
  - right. congruence. Defined.

#[global] Instance and_has_dec (A B : Prop)
  (d : HasDec A) (e : HasDec B) : HasDec (A /\ B).
Proof.
  destruct d as [x | x], e as [y | y].
  - left. intuition.
  - right. intuition.
  - right. intuition.
  - right. intuition. Defined.

#[global] Instance or_has_dec (A B : Prop)
  (d : HasDec A) (e : HasDec B) : HasDec (A \/ B).
Proof.
  destruct d as [x | x], e as [y | y].
  - left. intuition.
  - left. intuition.
  - left. intuition.
  - right. intuition. Defined.

#[global] Instance Forall_has_dec (A : Type) (P : A -> Prop)
  (d : forall x : A, HasDec (P x)) (a : list A) : HasDec (Forall P a) :=
  Forall_dec P d a.

#[global] Instance not_has_dec (A : Prop) (d : HasDec A) : HasDec (~ A) :=
  has_dec Decidable_not.

#[global] Instance Sexists_has_equiv_dec (A : Type) (P : A -> SProp)
  (e : HasEqDec A) : HasEqDec {x : A $ P x}.
Proof.
  intros [x a] [y b]. destruct (e x y) as [s | s].
  - left. apply Spr1_inj. unfold Spr1. apply s.
  - right. intros t. inversion t as [s']. congruence. Defined.
(* fun x y : {x : A $ P x} => eq_dec (Spr1 x) (Spr1 y). *)

Import ListNotations.

Arguments rev {_} _.

Lemma rev_nil (A : Type) (a : list A)
  (s : rev a = []) : a = [].
Proof.
  apply (f_equal rev) in s. rewrite rev_involutive in s.
  unfold rev in s. apply s. Qed.

Lemma rev_cons (A : Type) (x : A) (a b : list A)
  (s : rev a = x :: b) : a = rev b ++ [x].
Proof.
  apply (f_equal rev) in s. rewrite rev_involutive in s.
  change (rev (x :: b)) with (rev b ++ [x]) in s. apply s. Qed.

Lemma combine_snoc (A B : Type)
  (x : A) (a : list A) (y : B) (b : list B) (s : length a = length b) :
  combine (a ++ [x]) (b ++ [y]) = combine a b ++ [(x, y)].
Proof.
  revert y b s.
  induction a as [| z c t]; intros y [| w d] s.
  - reflexivity.
  - inversion s.
  - inversion s.
  - inversion s as [s']. pose proof fun y : B => t y _ s' as t'.
    cbn [combine app]. f_equal. apply t'. Qed.

Lemma combine_rev (A B : Type)
  (a : list A) (b : list B) (s : length a = length b) :
  combine (rev a) (rev b) = rev (combine a b).
Proof.
  revert b s.
  induction a as [| x c t]; intros [| y d] s.
  - reflexivity.
  - inversion s.
  - inversion s.
  - inversion s as [s']. pose proof t _ s' as t'.
    cbn [combine rev]. rewrite combine_snoc.
    + f_equal. apply t'.
    + repeat rewrite rev_length. apply s'. Qed.

(** We should use finger trees for this.
    It is possible to achieve constant time cons, snoc,
    logarithmic time append and linear time iteration.
    See the paper by Hinze and Paterson for details. *)

Section Context.

Lemma nth_nil (A : Type) (n : nat) (d : A) : nth n [] d = d.
Proof. destruct n as [| p]; reflexivity. Qed.

Lemma nth_firstn (A : Type) (n p : nat) (a : list A) (d : A) (s : n < p) :
  nth n (firstn p a) d = nth n a d.
Proof.
  revert n p d s.
  induction a as [| x b t]; intros n p d s; destruct n as [| q], p as [| r].
  - lia.
  - rewrite firstn_nil. reflexivity.
  - lia.
  - rewrite firstn_nil. reflexivity.
  - lia.
  - rewrite firstn_cons. reflexivity.
  - lia.
  - rewrite firstn_cons. apply t. lia. Qed.

Lemma nth_skipn (A : Type) (n p : nat) (a : list A) (d : A) (s : p < n) :
  nth n (skipn p a) d = nth (n - p) a d.
Proof.
  revert n p d s.
  induction a as [| x b t]; intros n p d s; destruct n as [| q], p as [| r].
  - lia.
  - lia.
  - rewrite skipn_nil. reflexivity.
  - rewrite skipn_nil. rewrite nth_overflow. cbn.
    destruct (q - r) as [| u]; reflexivity.
    unfold length. lia.
  - lia.
  - lia.
  - rewrite skipn_O. cbn. reflexivity.
  - rewrite skipn_cons.
    destruct r as [| u] eqn : p. Admitted.

Context (A : Type) {e : HasEqDec A}.

Equations wfb_def (a b : (bool * A)) : bool :=
  wfb_def (i, x) (j, y) := decide (~ (i <> j /\ x = y)).

#[local] Instance wfb_def_is_refl : IsRefl wfb_def.
Proof. intros [i x]. apply Decidable_complete. intuition. Qed.

#[local] Instance wfb_def_is_sym : IsSym wfb_def.
Proof.
  intros [i x] [j y] w. apply Decidable_sound in w.
  apply Decidable_complete. intuition. Qed.

Equations wfb (s : list (bool * A)) : bool :=
  wfb s := decide (Forall (prod_uncurry wfb_def) (combine s (skipn 1 s))).

Equations wf (s : list (bool * A)) : Prop :=
  wf s := forall (n : nat) (i j : bool) (x y : A),
    nth_error s n = Some (i, x) ->
    nth_error s (S n) = Some (j, y) ->
    ~ (i <> j /\ x = y).

Equations wf' (s : list (bool * A)) : Prop :=
  wf' s := forall (n : nat) (i j : bool) (x y : A) (d : bool * A),
    S n < length s ->
    nth n s d = (i, x) ->
    nth (S n) s d = (j, y) ->
    ~ (i <> j /\ x = y).

Lemma wf_iff_wf' (s : list (bool * A)) : wf s <-> wf' s.
Proof.
  split.
  - intros w. unfold wf, wf' in *. intros n i j x y [k z] b a0 a1.
    assert (c' : n < length s) by lia.
    epose proof nth_error_nth' _ _ c' as d0.
    epose proof nth_error_nth' _ _ b as d1.
    rewrite a0 in d0.
    rewrite a1 in d1.
    eauto.
  - intros w. unfold wf, wf' in *. intros n i j x y a0 a1.
    assert (d := (i, x)).
    epose proof nth_error_nth _ _ d a0 as d0.
    epose proof nth_error_nth _ _ d a1 as d1.
    assert (t0 : nth_error s n <> None) by congruence.
    assert (t1 : nth_error s (S n) <> None) by congruence.
    apply nth_error_Some in t0, t1. eauto. Qed.

Lemma wf_iff_wfb (s : list (bool * A)) : wf s <-> wfb s.
Proof.
  transitivity (wf' s).
  - apply wf_iff_wf'.
  - split.
    + intros w. unfold wf', wfb in *. apply Decidable_complete.
      apply Forall_nth. intros n d c.
      rewrite combine_firstn_r.
      unfold prod_uncurry. Admitted.

Equations free : Type :=
  free := {s : list (bool * A) | (wfb s)}.

Equations rel (x y : free) : bool :=
  rel (s; _) (t; _) := decide (s = t).

Equations null : free :=
  null := ([]; _).
Next Obligation. reflexivity. Qed.

Equations un (x : free) : free :=
  un (s; _) := (map (prod_bimap negb id) (rev s); _).
Next Obligation.
  intros s ws.
  apply Decidable_sound in ws.
  apply Decidable_complete.
  change (fun x : (bool * A) * (bool * A) => is_true (prod_uncurry wfb_def x))
  with (is_true o prod_uncurry wfb_def) in *.
  remember (length (skipn 1 (map (prod_bimap negb id) (rev s)))) as n eqn : an.
  rewrite combine_firstn_r.
  rewrite <- an.
  rewrite skipn_length in an.
  rewrite map_length in an.
  rewrite rev_length in an.
  rewrite map_rev.
  rewrite firstn_rev.
  rewrite skipn_rev.
  rewrite map_length.
  rewrite combine_rev.
  2:{ rewrite skipn_length. rewrite firstn_length.
    destruct s. reflexivity. cbn in an.
    rewrite Nat.sub_0_r in an. rewrite an. cbn [length].
    rewrite Nat.sub_succ_l by lia.
    rewrite Nat.sub_diag. cbn. repeat rewrite Nat.sub_0_r.
    rewrite map_length. lia. }
  apply Forall_rev.
  rewrite an. clear n an.
  induction s as [| [i x] t w].
  - apply Forall_nil.
  - cbn [length].
    replace (S (length t) - (S (length t) - 1)) with (S O) by lia.
    replace (S (length t) - 1) with (length t) by lia.
    destruct t as [| [j y] u].
    + apply Forall_nil.
    + cbn. apply Forall_cons.
      * apply Forall_inv in ws. apply Decidable_sound in ws.
        apply Decidable_complete. intros [ji yx]. apply ws.
        split. intros ij. apply ji. apply f_equal. auto. auto.
      * cbn in ws. apply Forall_inv_tail in ws.
        apply w in ws. clear w.
        cbn [length] in ws.
        replace (S (length u) - (S (length u) - 1)) with (S O) in ws by lia.
        replace (S (length u) - 1) with (length u) in ws by lia.
        rewrite skipn_map in ws. cbn [skipn] in ws.
        cbn [map prod_bimap] in ws. apply ws. Qed.

Equations bin_fix (s t : list (bool * A)) :
  list (bool * A) * list (bool * A) by struct t :=
  bin_fix [] b := ([], b);
  bin_fix a [] := (a, []);
  bin_fix (a :: s) (b :: t) with wfb_def a b :=
    | true => (a :: s, b :: t)
    | false => bin_fix s t.

Equations bin (x y : free) : free :=
  (* bin (s; _) (t; _) with bin_fix (rev s) t :=
    | (u, v) => (app (rev u) v; _). *)
  bin (s; _) (t; _) with (bin_fix (rev s) t; eq_refl) :=
    | ((u, v); _) => (app (rev u) v; _).
Next Obligation.
  intros s ws t u v a wt.
  apply Decidable_sound in ws, wt.
  apply Decidable_complete.
  change (fun x : (bool * A) * (bool * A) => is_true (prod_uncurry wfb_def x))
  with (is_true o prod_uncurry wfb_def) in *.
  remember (length (skipn 1 (rev u ++ v))) as n eqn : an.
  rewrite combine_firstn_r.
  rewrite <- an.
  rewrite <- (rev_involutive v).
  rewrite <- rev_app_distr.
  rewrite firstn_rev.
  rewrite skipn_rev.
  rewrite combine_rev.
  2:{ rewrite skipn_length. rewrite firstn_length.
    destruct u. cbn [rev app] in *. rewrite app_nil_r in *.
    rewrite skipn_length in an.
    rewrite rev_length. lia.
    rewrite skipn_length in an.
    rewrite app_length in *.
    rewrite rev_length in *.
    cbn [length] in *. lia. }
  apply Forall_rev.
  rewrite an.
  clear n an.
  rewrite skipn_length.
  destruct s. cbn in a. rewrite bin_fix_equation_1 in a.
  inversion a as [[a0 a1]]. subst. cbn [rev length app].
  rewrite app_nil_r. rewrite rev_length.
  destruct v. apply Forall_nil. cbn [rev length app].
  replace (S (length v) - (S (length v) - 1)) with (S O) by lia.
  replace (S (length v) - 1) with (length v) by lia.
  cbn [skipn] in wt. rewrite skipn_app. rewrite firstn_app.
  rewrite <- (rev_length v).
  rewrite firstn_all. rewrite Nat.sub_diag. rewrite firstn_O.
  rewrite app_nil_r. destruct v. apply Forall_nil. rewrite rev_length.
  cbn [length]. replace (1 - length (p0 :: v)) with O by reflexivity.
  rewrite skipn_O. Admitted.

#[local] Instance has_equiv_rel : HasEquivRel free := eq.
#[local] Instance has_null_op : HasNullOp free := null.
#[local] Instance has_un_op : HasUnOp free := un.
#[local] Instance has_bin_op : HasBinOp free := bin.

#[local] Instance is_grp : IsGrp eq null un bin.
Proof.
  esplit.
  - esplit.
    + esplit.
      * esplit.
        -- admit.
        -- admit.
        -- admit.
      * admit.
      * admit.
    + esplit.
      * admit.
      * admit.
  - esplit.
    + admit.
    + admit.
  - admit. Admitted.

End Context.

Arguments free _ {_}.

#[export] Hint Resolve has_equiv_rel
  has_null_op has_un_op has_bin_op is_grp : typeclass_instances.

Section Context.

Context (A : Type) {e : HasEqDec A} (f : A -> Z).

Equations eval_Z_add_def (a : bool * A) : Z :=
  eval_Z_add_def (false, x) := f x;
  eval_Z_add_def (true, x) := Z.opp (f x).

Equations eval_Z_add (s : free A) : Z :=
  eval_Z_add (s; _) := fold_right Z.add Z.zero (map eval_Z_add_def s).

#[local] Instance is_grp_hom :
  IsGrpHom eq null un bin eq Z.zero Z.opp Z.add eval_Z_add.
Proof.
  esplit.
  - apply is_grp.
  - apply Additive.is_grp.
  - intros z w. unfold eval_Z_add. admit.
  - intros [z ?] [w ?]. unfold rel. destruct (eq_dec z w).
    + intros _. unfold eval_Z_add, proj1_sig. rewrite e0. reflexivity.
    + intros a. inversion a. Admitted.

End Context.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A)
  `{!IsGrp X x f k}.

Equations const_tt (x : A) : unit :=
  const_tt _ := tt.

#[local] Instance is_grp_hom' :
  IsGrpHom X x f k eq tt tt1 tt2 const_tt.
Proof.
  esplit.
  - typeclasses eauto.
  - typeclasses eauto.
  - intros ? ?. reflexivity.
  - intros ? ? _. reflexivity. Qed.

End Context.

End Mess.
