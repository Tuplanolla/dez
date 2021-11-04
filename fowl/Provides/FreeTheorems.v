(** * Free Structure *)

From Coq Require Import
  Extraction Lists.List ZArith.ZArith.
From DEZ.Has Require Export
  Decidability Unsquashing.
From DEZ.Is Require Export
  Group Truncated.
From DEZ.Provides Require Export
  BooleanTheorems UnitTheorems ZTheorems.
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

Section Context.

Context (A : Type) (d : forall x y : A, {x = y} + {x <> y}).

#[local] Instance has_eq_dec : HasEqDec A := d.

Equations wfb (t : (bool * A) * (bool * A)) : bool :=
  wfb ((x, a), (y, b)) := decide (~ (x <> y /\ a = b)).

Equations free_wfb (s : list (bool * A)) : bool :=
  free_wfb s := decide (Forall wfb (combine s (skipn 1 s))).

(** We should use finger trees for this.
    It is possible to achieve constant time cons, snoc,
    logarithmic time append and linear time iteration.
    See the paper by Hinze and Paterson for details. *)

Equations free : Type :=
  free := {s : list (bool * A) $ Squash (free_wfb s)}.

Equations rel (s t : free) : Prop :=
  rel (Sexists _ s _) (Sexists _ t _) := is_left (eq_dec s t).

Equations null : free :=
  null := Sexists _ [] _.
Next Obligation. apply squash. reflexivity. Qed.

Equations un_fix (t s : list (bool * A)) : list (bool * A) by struct s :=
  un_fix t [] := t;
  un_fix t ((x, a) :: s) := un_fix ((negb x, a) :: t) s.

Equations un (s : free) : free :=
  un (Sexists _ s _) := Sexists _ (un_fix [] s) _.
Next Obligation.
  intros s w. apply unsquash in w. unfold free_wfb in w.
  apply Decidable_sound in w. apply squash. apply Decidable_complete.
  change (fun t : (bool * A) * (bool * A) => is_true (wfb t))
  with (is_true o wfb) in *.
  induction s as [| [x a] [| [y b] t] v].
  - unfold combine, un_fix, skipn. apply Forall_nil.
  - unfold combine, un_fix, skipn. apply Forall_nil.
  - replace (combine ((x, a) :: (y, b) :: t) (skipn 1 ((x, a) :: (y, b) :: t)))
    with (((x, a), (y, b)) :: combine ((y, b) :: t) t) in w by reflexivity.
    pose proof Forall_inv w as u.
    pose proof v (Forall_inv_tail w) as u_tail. Admitted.

Equations bin_fix (s t : list (bool * A)) :
  list (bool * A) * list (bool * A) by struct t :=
  bin_fix [] b := ([], b);
  bin_fix a [] := (a, []);
  bin_fix ((i, x) :: xs) ((j, y) :: ys) with decide (i = j /\ x = y) := {
    | true => bin_fix xs ys;
    | false => ((i, x) :: xs, (j, y) :: ys)
  }.

Equations bin (s t : free) : free :=
  bin (Sexists _ a _) (Sexists _ b _) :=
  let (s, t) := bin_fix (un_fix [] a) b in
  Sexists _ (un_fix [] s ++ t) _.
Next Obligation.
  intros a wa b wb s t.
  apply unsquash in wa, wb. unfold free_wfb in wa, wb.
  apply Decidable_sound in wa, wb. apply squash. apply Decidable_complete.
  change (fun t : (bool * A) * (bool * A) => is_true (wfb t))
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

Section Context.

Context (A : Type) (d : forall x y : A, {x = y} + {x <> y}) (f : A -> Z).

#[local] Instance again_has_eq_dec : HasEqDec A := d.
#[local] Instance Z_has_eq_dec : HasEqDec Z := Z.eq_dec.

#[local] Open Scope Z_scope.

Definition hm (s : free d) : Z :=
  fold_right Z.add Z.zero
  (map (fun t : bool * A => let (x, a) := t in
  if x then Z.opp (f a) else f a) (Spr1 s)).

#[local] Instance is_grp_hom :
  IsGrpHom (rel eq_dec) (null eq_dec) (un eq_dec) (bin eq_dec)
  eq Z.zero Z.opp Z.add hm.
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
  un (Sexists_has_eq_dec Z.eq_dec)
  (Sexists (Squash o free_wfb Z.eq_dec)
  [b; a'; c; a; c'; b; b] _).

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
  bin Z.eq_dec [b; a'; c; a'] [a; c'; b; b].

Compute
  let a := (false, 1) in
  let b := (false, 2) in
  let c := (false, 3) in
  let a' := (negb (fst a), snd a) in
  let b' := (negb (fst b), snd b) in
  let c' := (negb (fst c), snd c) in
  (fold_right Z.add Z.zero [2; -1; 3; -1; 1; -3; 2; 2],
  hm (bin Z.eq_dec [b; a'; c; a'] [a; c'; b; b])).

(* Extraction Mess. *)
