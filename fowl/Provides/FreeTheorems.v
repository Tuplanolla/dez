(** * Free Structure *)

From Coq Require Import
  Extraction Lia Lists.List ZArith.ZArith.
From DEZ.Has Require Export
  Decidability Unsquashing.
From DEZ.Is Require Export
  Group Truncated.
From DEZ.Provides Require Export
  BooleanTheorems ProductTheorems UnitTheorems ZTheorems.
From DEZ.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Module Mess.

#[global] Instance prod_has_eq_dec (A B : Type)
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

#[local] Instance Forall_has_dec (A : Type) (P : A -> Prop)
  (d : forall x : A, HasDec (P x)) (a : list A) : HasDec (Forall P a) :=
  Forall_dec P d a.

#[local] Instance not_has_dec (A : Prop) (d : HasDec A) : HasDec (~ A) :=
  has_dec Decidable_not.

#[local] Instance Sexists_has_eq_dec (A : Type) (P : A -> SProp)
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

Context (A : Type) {d : HasEqDec A}.

Equations wfb (a : (bool * A) * (bool * A)) : bool :=
  wfb ((i, x), (j, y)) := decide (~ (i <> j /\ x = y)).

Equations free_wfb (s : list (bool * A)) : bool :=
  free_wfb s := decide (Forall wfb (combine s (skipn 1 s))).

Equations free : Type :=
  free := {s : list (bool * A) $ Squash (free_wfb s)}.

#[local] Notation "'(' x ';' a ')'" := (Sexists _ x a).

Equations rel (x y : free) : Prop :=
  rel (s; _) (t; _) := decide (s = t).

Equations null : free :=
  null := ([]; _).
Next Obligation. apply squash. reflexivity. Qed.

Equations un (x : free) : free :=
  un (s; _) := (map (prod_bimap negb id) (rev s); _).
Next Obligation.
  intros s ws.
  apply unsquash in ws. apply Decidable_sound in ws.
  apply squash. apply Decidable_complete.
  change (fun x : (bool * A) * (bool * A) => is_true (wfb x))
  with (is_true o wfb) in *.
  induction s as [| [i x] [| [j y] u] w].
  - apply Forall_nil.
  - apply Forall_nil.
  - rewrite map_rev. rewrite combine_firstn_r.
  remember (map (prod_bimap negb id) ((i, x) :: (j, y) :: u)) as a.
    rewrite skipn_rev.
    rewrite rev_length.
    rewrite firstn_rev.
    rewrite firstn_length_le by lia.
    replace (length a - (length a - 1)) with 1%nat.
    2:{ subst a. cbn. destruct (length (map (prod_bimap negb id) u)); lia. }
    Search firstn length.
    subst a.
    rewrite map_length.
    rewrite combine_rev.
    2:{ cbn. rewrite map_length. f_equal. rewrite firstn_length_le. reflexivity.
      cbn. rewrite map_length. lia. }
    apply Forall_rev. cbn.
    apply Forall_cons.
    + apply Forall_inv in ws. apply Decidable_sound in ws.
      apply Decidable_complete. intros [ji yx]. apply ws.
      split. intros ij. apply ji. apply f_equal. auto. auto.
    + apply Forall_inv_tail in ws.
      apply w in ws. clear w. Admitted.

Equations bin_fix (s t : list (bool * A)) :
  list (bool * A) * list (bool * A) by struct t :=
  bin_fix [] b := ([], b);
  bin_fix a [] := (a, []);
  bin_fix ((i, x) :: a) ((j, y) :: b) with decide (i <> j /\ x = y) := {
    | true => bin_fix a b
    | false => ((i, x) :: a, (j, y) :: b)
  }.

Equations bin (x y : free) : free :=
  bin (s; _) (t; _) :=
  let (s', t') := bin_fix (rev s) t in
  (rev s' ++ t'; _).
Next Obligation.
  intros s ws t wt s' t'.
  apply unsquash in ws, wt. apply Decidable_sound in ws, wt.
  apply squash. apply Decidable_complete.
  change (fun x : (bool * A) * (bool * A) => is_true (wfb x))
  with (is_true o wfb) in *. Admitted.

#[local] Instance is_grp : IsGrp rel null un bin.
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

Section Context.

Context (A : Type) {d : HasEqDec A} (f : A -> Z).

#[local] Open Scope Z_scope.

Definition hm (s : free A) : Z :=
  fold_right Z.add Z.zero
  (map (fun t : bool * A => let (x, a) := t in
  if x then Z.opp (f a) else f a) (Spr1 s)).

#[local] Instance is_grp_hom :
  IsGrpHom rel null un bin eq Z.zero Z.opp Z.add hm.
Proof.
  esplit.
  - apply is_grp.
  - apply Additive.is_grp.
  - intros z w. unfold hm. admit.
  - intros [z ?] [w ?]. unfold rel. destruct (eq_dec z w).
    + intros _. unfold hm, Spr1. rewrite e. reflexivity.
    + intros a. inversion a. Admitted.

Equations tt1 (x : unit) : unit :=
  tt1 _ := tt.

Equations tt2 (x y : unit) : unit :=
  tt2 _ _ := tt.

Equations const_tt (x : Z) : unit :=
  const_tt _ := tt.

#[local] Instance is_grp_hom' :
  IsGrpHom eq Z.zero Z.opp Z.add eq tt tt1 tt2 const_tt.
Proof.
  esplit.
  - (** Yes, [+%Z] forms a group. *) admit.
  - (** Yes, [+%unit] forms a group. *) admit.
  - intros ? ?. reflexivity.
  - intros ? ? _. reflexivity. Admitted.

End Context.

End Mess.

Import ListNotations.

#[local] Open Scope Z_scope.

(* - (b a' c a c' b b) *)
(* b' b' c a' c' a b' *)

Compute
  let a := (false, 1) in
  let b := (false, 2) in
  let c := (false, 3) in
  let a' := (negb (fst a), snd a) in
  let b' := (negb (fst b), snd b) in
  let c' := (negb (fst c), snd c) in
  Mess.un (Sexists _ [b; a'; c; a; c'; b; b] _).

(* b a' c a' + a c' b b *)
(* b a' c + c' b b *)
(* b a' + b b *)
(* b a' b b *)

Compute
  let a := (false, 1) in
  let b := (false, 2) in
  let c := (false, 3) in
  let a' := (negb (fst a), snd a) in
  let b' := (negb (fst b), snd b) in
  let c' := (negb (fst c), snd c) in
  Mess.bin [b; a'; c; a'] [a; c'; b; b].

Compute
  let a := (false, 1) in
  let b := (false, 2) in
  let c := (false, 3) in
  let a' := (negb (fst a), snd a) in
  let b' := (negb (fst b), snd b) in
  let c' := (negb (fst c), snd c) in
  (fold_right Z.add Z.zero [2; -1; 3; -1; 1; -3; 2; 2],
  Mess.hm (Mess.bin [b; a'; c; a'] [a; c'; b; b])).

(* Extraction Mess. *)
