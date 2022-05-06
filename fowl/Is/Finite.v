(** * Finiteness *)

From Coq Require Import
  Lia Lists.List Logic.FinFun NArith.NArith.
From DEZ.Has Require Export
  EquivalenceRelations Decisions Enumerations Cardinalities.
From DEZ.Is Require Export
  Isomorphic Extensional Truncated.
From DEZ.Justifies Require Export
  OptionTheorems ProductTheorems LogicalTheorems NTheorems.
From DEZ.Provides Require Import
  TypeclassTactics.
From DEZ.Supports Require Import
  EquivalenceNotations.

Import ListNotations.

#[local] Open Scope relation_scope.
#[local] Open Scope core_scope.
#[local] Open Scope sig_scope.
#[local] Open Scope N_scope.

(** TODO This does not belong here! *)

Equations comparison_eq_dec (x y : comparison) : {x = y} + {x <> y} :=
  comparison_eq_dec Eq Eq := left _;
  comparison_eq_dec Lt Lt := left _;
  comparison_eq_dec Gt Gt := left _;
  comparison_eq_dec _ _ := right _.
Next Obligation. intros x y a. discriminate. Qed.
Next Obligation. intros x y a. discriminate. Qed.
Next Obligation. intros x y a. discriminate. Qed.
Next Obligation. intros x y a. discriminate. Qed.
Next Obligation. intros x y a. discriminate. Qed.
Next Obligation. intros x y a. discriminate. Qed.

#[export] Instance comparison_is_has_eq_dec : HasEqDec comparison :=
  comparison_eq_dec.

#[local] Instance comparison_is_set : IsSet comparison.
Proof. typeclasses eauto. Qed.

#[export] Instance N_lt_is_prop (n p : N) : IsProp (p < n).
Proof. intros a b. apply uip. Qed.

Module Ref'.

Section Context.

Context (A : Type).

Equations N_length (a : list A) : N :=
  N_length a := N.of_nat (length a).

Equations Nth (n : N) (a : list A) (x : A) : A :=
  Nth n := nth (N.to_nat n).

Equations N_seq (n p : N) : list N :=
  N_seq n p := map N.of_nat (seq (N.to_nat n) (N.to_nat p)).

End Context.

End Ref'.

Section Context.

Equations N_seq (n p : N) : list N by wf p N.lt :=
  N_seq n N0 := [];
  N_seq n p := n :: N_seq (N.succ n) (N.pred p).
Next Obligation. intros n p r q. lia. Qed.

Context (A : Type).

Equations N_length (a : list A) : N by struct a :=
  N_length [] := 0;
  N_length (x :: b) := N.succ (N_length b).

Equations Nth (n : N) (a : list A) (x : A) : A by struct a :=
  Nth _ [] x := x;
  Nth N0 (y :: _) _ := y;
  Nth n (y :: b) x := Nth (N.pred n) b x.

End Context.

Lemma N_length_ref (A : Type) (a : list A) :
  N_length a = Ref'.N_length a.
Proof.
  apply Ref'.N_length_elim. clear a. intros a. apply N_length_elim.
  - clear a. reflexivity.
  - clear a. intros x b s.
    simpl length. rewrite Nat2N.inj_succ. f_equal. apply s. Qed.

Lemma Nth_ref (A : Type) (n : N) (a : list A) (x : A) :
  Nth n a x = Ref'.Nth n a x.
Proof.
  apply Ref'.Nth_elim. clear n. intros n. apply Nth_elim.
  - clear x n. intros n x. destruct n as [| p _] using N.peano_ind.
    + reflexivity.
    + rewrite N2Nat.inj_succ. reflexivity.
  - clear x n. intros y n x. reflexivity.
  - clear x n. intros p y b x s.
    rewrite N2Nat.inj_pred in s. destruct (N.to_nat (N.pos p)) as [| q] eqn : t.
    + lia.
    + apply s. Qed.

Lemma N_seq_ref (n p : N) :
  N_seq n p = Ref'.N_seq n p.
Proof.
  apply Ref'.N_seq_elim. clear n p. intros n p.
  revert n. induction p as [| q s] using N.peano_ind; intros n.
  - reflexivity.
  - rewrite N2Nat.inj_succ. simpl seq. simpl map.
    pose proof s (N.succ n) as s'. rewrite N2Nat.inj_succ in s'.
    rewrite N2Nat.id. rewrite <- N.succ_pos_spec. simp N_seq.
    rewrite N.succ_pos_spec. rewrite N.pred_succ. f_equal. apply s'. Qed.

Section Context.

Context (A : Type) {X : HasEquivRel A} {d : HasEquivDec A}
  `{!IsEquiv X}.

Ltac notations f := progress (
  f X (equiv_rel (A := A));
  f d (equiv_dec (A := A))).

Equations is_in (x : A) (a : list A) : bool :=
  is_in _ [] := false;
  is_in x (y :: b) := is_left (dec (x == y)) || is_in x b.

(** ** List Membership *)

(** This is a generalization of [In]. *)

Equations IsIn (x : A) (a : list A) : Prop :=
  IsIn _ [] := False;
  IsIn x (y :: b) := x == y \/ IsIn x b.

Lemma Exists_IsIn (P : A -> Prop) (a : list A) (s : Exists P a) :
  exists x : A, IsIn x a /\ P x.
Proof.
  induction s as [x b s | x b _ [y [i s]]].
  - exists x. split.
    + left. reflexivity.
    + apply s.
  - exists y. split.
    + right. apply i.
    + apply s. Qed.

Lemma Proper_IsIn (x y : A) (a : list A)
  (s : x == y) (t : IsIn x a) : IsIn y a.
Proof.
  induction a as [| z b u].
  - contradiction.
  - destruct t as [v | v].
    + left. rewrite <- s, <- v. reflexivity.
    + right. apply u. apply v. Qed.

Lemma nth_IsIn (n : nat) (a : list A) (y : A) :
  (n < length a)%nat -> IsIn (nth n a y) a.
Proof.
  revert a; induction n as [| p s]; intros a t.
  - destruct a as [| z b]. simpl in t; lia.
    simpl. left. reflexivity.
  - destruct a as [| z b]. simpl in t; lia.
    simpl. right. apply s. simpl in t; lia. Qed.

Equations nfind_from (n : nat) (x : A) (a : list A) : option nat :=
  nfind_from _ _ [] := None;
  nfind_from n x (y :: b) with dec (x == y) := {
    | left _ := Some n
    | right _ := nfind_from (S n) x b
  }.

Equations nfind (x : A) (a : list A) : option nat :=
  nfind := nfind_from 0.

Lemma Nth_succ (n : N) (y : A) (b : list A) (x : A) :
  Nth (N.succ n) (y :: b) x = Nth n b x.
Proof.
  destruct n as [| p].
  - simp Nth. simpl N.pred. reflexivity.
  - simp Nth. simpl N.pred. rewrite Pos.pred_N_succ. reflexivity. Qed.

Equations Nfind_from (n : N) (x : A) (a : list A) : option N :=
  Nfind_from _ _ [] := None;
  Nfind_from n x (y :: b) with dec (x == y) := {
    | left _ := Some n
    | right _ := Nfind_from (N.succ n) x b
  }.

Lemma Nfind_from_succ (n p : N) (x : A) (a : list A)
  (e : Nfind_from n x a = Some p) : Nfind_from (N.succ n) x a = Some (N.succ p).
Proof.
  revert e. apply Nfind_from_elim.
  - clear n x a. intros n x e.
    discriminate.
  - clear n x a. intros n x y ex b ed e.
    simp Nfind_from. rewrite ed. simpl.
    inversion_clear e. reflexivity.
  - clear n x a. intros n x y ex b es ed e.
    simp Nfind_from. rewrite ed. simpl.
    apply es. apply e. Qed.

Lemma Nfind_from_succ' (n p : N) (x : A) (a : list A)
  (e : Nfind_from (N.succ n) x a = Some (N.succ p)) : Nfind_from n x a = Some p.
Proof.
  revert e. apply (Nfind_from_elim
  (fun (n : N) (x : A) (a : list A) (s : option N) =>
  Nfind_from (N.succ n) x a = Some (N.succ p) -> s = Some p)).
  - clear n x a. intros n x e.
    discriminate.
  - clear n x a. intros n x y ex b ed e.
    simp Nfind_from in e. rewrite ed in e. simpl in e.
    f_equal. apply N.succ_inj. inversion_clear e. reflexivity.
  - clear n x a. intros n x y ex b es ed e.
    simp Nfind_from in e. rewrite ed in e. simpl in e.
    apply es. apply e. Qed.

Lemma Nfind_from_succ_iff (n p : N) (x : A) (a : list A) :
  Nfind_from n x a = Some p <-> Nfind_from (N.succ n) x a = Some (N.succ p).
Proof.
  split.
  - apply Nfind_from_succ.
  - apply Nfind_from_succ'. Qed.

Lemma Nfind_from_succ_zero (n : N) (x : A) (a : list A)
  (e : Nfind_from (N.succ n) x a = Some 0) : 0.
Proof.
  revert e. apply (Nfind_from_elim
  (fun (n : N) (x : A) (a : list A) (s : option N) =>
  Nfind_from (N.succ n) x a = Some 0 -> 0)).
  - clear n x a. intros n x e.
    discriminate.
  - clear n x a. intros n x y ex b ed e.
    simp Nfind_from in e. rewrite ed in e. simpl in e.
    injection e. lia.
  - clear n x a. intros n x y ex b f ed e.
    simp Nfind_from in e. rewrite ed in e. simpl in e.
    apply f. apply e. Qed.

Lemma Nfind_from_lt (n p : N) (x : A) (a : list A)
  (i : p < n) (e : Nfind_from n x a = Some p) : 0.
Proof.
  revert p i e. induction n as [| q f] using N.peano_ind; intros p i e.
  - lia.
  - destruct p as [| r _] using N.peano_ind.
    + apply Nfind_from_succ_zero in e. contradiction.
    + apply Nfind_from_succ' in e. apply f in e.
      * contradiction.
      * lia. Qed.

Lemma Nfind_from_some (n p : N) (x y : A) (a : list A)
  (e : Nfind_from n x a = Some (n + p)) :
  IsIn x a /\ p < N_length a /\ Nth p a y == x.
Proof.
  revert n p e. induction a as [| z b c]; intros n p e.
  - discriminate.
  - destruct p as [| q _] using N.peano_ind.
    + destruct (dec (x == z)) as [ex | fx] eqn : ed.
      * split.
        -- left. apply ex.
        -- split.
           ++ simpl N_length. lia.
           ++ symmetry. apply ex.
      * exfalso.
        simp Nfind_from in e. rewrite ed in e. simpl in e.
        apply Nfind_from_lt in e.
        -- contradiction.
        -- lia.
    + destruct (dec (x == z)) as [ex | fx] eqn : ed.
      * exfalso. simp Nfind_from in e. rewrite ed in e. simpl in e.
        injection e. lia.
      * simp Nfind_from in e. rewrite ed in e. simpl in e.
        pose proof c (N.succ n) q as cq.
        rewrite <- N.add_succ_comm in e. apply cq in e. destruct e as [i [iq ex]].
        split.
        -- right. apply i.
        -- split.
           ++ simp N_length. lia.
           ++ rewrite Nth_succ. apply ex. Qed.

Lemma Nfind_from_none (n : N) (x : A) (a : list A)
  (e : Nfind_from n x a = None) : ~ IsIn x a.
Proof.
  revert n e. induction a as [| z b c]; intros n e.
  - intros s. contradiction.
  - intros s. simpl in s. destruct s as [t | t].
    + destruct (dec (x == z)) as [ex | fx] eqn : ed.
      * exfalso. simp Nfind_from in e. rewrite ed in e. simpl in e.
        discriminate.
      * contradiction.
    + destruct (dec (x == z)) as [ex | fx] eqn : ed.
      * simp Nfind_from in e. rewrite ed in e. simpl in e.
        discriminate.
      * simp Nfind_from in e. rewrite ed in e. simpl in e.
        revert t. eapply c. apply e. Qed.

Equations Nfind (x : A) (a : list A) : option N :=
  Nfind := Nfind_from 0.

Lemma Nfind_some (x y : A) (a : list A) (n : N) (s : Nfind x a = Some n) :
  IsIn x a /\ n < N_length a /\ Nth n a y == x.
Proof. eapply Nfind_from_some. rewrite N.add_0_l. apply s. Qed.

Lemma Nfind_none (x : A) (a : list A)
  (s : Nfind x a = None) (i : IsIn x a) : 0.
Proof. eapply Nfind_from_none. apply s. apply i. Qed.

End Context.

(** ** Unsorted Enumeration of a Type *)

(** This is a generalization of [Full]. *)

Class IsFull (A : Type) (X : A -> A -> Prop) (a : list A) : Prop :=
  full (x : A) : Exists (X x) a.

(** ** Uniqueness of a Listing *)

(** This is a generalization of [NoDup]. *)

Inductive IsNoDup (A : Type) (X : A -> A -> Prop) : list A -> Prop :=
  | IsNoDup_nil : IsNoDup X []
  | IsNoDup_cons (x : A) (a : list A) (s : ~ IsIn (X := X) x a)
    (t : IsNoDup X a) : IsNoDup X (x :: a).

Existing Class IsNoDup.

(** ** Unsorted Unique Enumeration of a Type *)

(** This is a generalization of [Listing]. *)

Class IsListing (A : Type) (X : A -> A -> Prop) (a : list A) : Prop := {
  listing_is_full :> IsFull X a;
  listing_is_no_dup :> IsNoDup X a;
}.

(** ** Finiteness in Terms of Enumeration *)

Class IsFinFull (A : Type) (X : A -> A -> Prop) : Prop :=
  fin_full : exists a : list A, IsFull X a.

#[export] Instance full_is_fin_full (A : Type) (X : A -> A -> Prop)
  (a : list A) `{!IsFull X a} : IsFinFull X.
Proof. exists a. auto. Qed.

(** ** Finiteness in Terms of Unique Enumeration *)

Class IsFinListing (A : Type) (X : A -> A -> Prop) : Prop :=
  fin_listing : exists a : list A, IsListing X a.

#[export] Instance listing_is_fin_listing (A : Type) (X : A -> A -> Prop)
  (a : list A) `{!IsListing X a} : IsFinListing X.
Proof. exists a. auto. Qed.

(** ** Size of a Type *)

Class IsSize (A : Type) (X : A -> A -> Prop) (n : N) : Prop :=
  size_is_equiv_types :> IsEquivTypes {p : N | p < n} A _=_ X.

(** ** Finiteness in Terms of Counting *)

Class IsFinSize (A : Type) (X : A -> A -> Prop) : Prop :=
  fin_size : exists n : N, IsSize X n.

#[export] Instance size_is_fin_size (A : Type) (X : A -> A -> Prop)
  (n : N) `{!IsSize X n} : IsFinSize X.
Proof. exists n. auto. Qed.

(** TODO The rest is not in the diagram yet. *)

(** This reference implementation is simpler to use in proofs;
    the other implementation is faster to use in computations. *)

Module Ref.

Section Context.

Context (A : Type).

Equations index_from (n : N) (a : list A) : list (N * A) :=
  index_from n a := combine (map N.of_nat (seq (N.to_nat n) (length a))) a.

Equations index (a : list A) : list (N * A) :=
  index := index_from 0.

End Context.

End Ref.

Section Context.

Context (A : Type).

Equations index_from (n : N) (a : list A) : list (N * A) by struct a :=
  index_from _ [] := [];
  index_from n (x :: b) := (n, x) :: index_from (N.succ n) b.

Equations index (a : list A) : list (N * A) :=
  index := index_from 0.

End Context.

Section Context.

Context (A : Type).

Lemma index_from_ref (n : N) (a : list A) :
  index_from n a = Ref.index_from n a.
Proof.
  apply Ref.index_from_elim. clear n a. intros n a. apply index_from_elim.
  - clear n a. intros n. reflexivity.
  - clear n a. intros n x a s.
    cbn [length seq map combine].
    rewrite N2Nat.id. f_equal.
    rewrite s. rewrite N2Nat.inj_succ. reflexivity. Qed.

Lemma index_ref (a : list A) : index a = Ref.index a.
Proof. apply Ref.index_elim. apply index_elim. apply index_from_ref. Qed.

End Context.

Lemma index_In (A : Type)
  (n : N) (x : A) (a : list A) (s : In (n, x) (index a)) :
  n < N.of_nat (length a).
Proof.
  rewrite index_ref in s. unfold Ref.index, Ref.index_from in s.
  apply in_combine_l in s. apply (in_map N.to_nat) in s.
  rewrite map_map in s. rewrite (map_ext _ id) in s.
  - rewrite map_id in s. apply in_seq in s. lia.
  - intros p. rewrite Nat2N.id. reflexivity. Qed.

Lemma index_length (A : Type) (a : list A) : length (index a) = length a.
Proof.
  rewrite index_ref. unfold Ref.index, Ref.index_from.
  rewrite combine_length. rewrite map_length. rewrite seq_length.
  rewrite Min.min_idempotent. reflexivity. Qed.

Lemma index_nth (A : Type)
  (n : N) (x : A) (a : list A) (s : n < N.of_nat (length a)) :
  nth (N.to_nat n) (index a) (N.of_nat 0, x) = (n, nth (N.to_nat n) a x).
Proof.
  rewrite index_ref. unfold Ref.index.
  rewrite combine_nth.
  - f_equal.
    + rewrite map_nth. rewrite seq_nth.
      * lia.
      * lia.
  - rewrite map_length. rewrite seq_length. reflexivity. Qed.

Section Context.

Context (A : Type) {X : HasEquivRel A} {d : HasEquivDec A} {a : HasEnum A}
  `{!IsEquiv X} `{!IsFull X a}.

Ltac notations f := progress (
  f X (equiv_rel (A := A));
  f d (equiv_dec (A := A));
  f a (enum A)).

Equations encode (s : {p : N | p < N.of_nat (length (enum A))}) : A :=
  encode (p; t) with inspect (enum A) := {
    | [] eqn : _ => _
    | x :: b eqn : _ => snd (nth (N.to_nat p) (index (x :: b)) (0, x))
  }.
Next Obligation with notations enabled.
  cbv beta...
  intros p t u. rewrite u in t. unfold length, N.of_nat in t. lia. Qed.

Equations decode (x : A) : {p : N | p < N.of_nat (length (enum A))} :=
  decode x with inspect (Nfind x (enum A)) := {
    | Some p eqn : _ => (p; _)
    | None eqn : _ => _
  }.
Next Obligation with notations enabled.
  cbv beta...
  intros x p s. apply (Nfind_some x x (enum A)) in s.
  destruct s as [i [ip ex]]. rewrite N_length_ref in ip. apply ip. Qed.
Next Obligation with notations enabled.
  cbv beta...
  intros x t. exfalso.
  apply (Nfind_none x a).
  - apply t.
  - pose proof full x as u. apply Exists_exists in u. destruct u as [y [v w]].
    idtac...
    clear IsEquiv0 IsFull0 t.
    induction (enum A) as [| z b u].
    + contradiction.
    + destruct v as [v0 | v1].
      * left. rewrite v0. apply w.
      * right. apply u. apply v1. Qed.

Lemma nth_inversion `{!IsNoDup X a} (n p : nat) (x : A)
  (inl : (n < length (enum A))%nat) (ipl : (p < length (enum A))%nat)
  (s : nth n (enum A) x == nth p (enum A) x) : n = p.
Proof with notations enabled.
  idtac...
  clear IsFull0.
  revert n p s inl ipl; induction IsNoDup0 as [| y b f t u]; intros n p s inl ipl.
  - simpl in inl; lia.
  - destruct n as [| q], p as [| r].
    + reflexivity.
    + simpl in s. exfalso. apply f. eapply Proper_IsIn.
      symmetry; apply s. apply nth_IsIn. simpl in ipl; lia.
    + simpl in s. exfalso. apply f. eapply Proper_IsIn.
      apply s. apply nth_IsIn. simpl in inl; lia.
    + f_equal. simpl in s. apply u. apply s.
      simpl in inl; lia. simpl in ipl; lia. Qed.

End Context.

#[export] Instance prod_has_equiv_rel (A B : Type)
  {X : HasEquivRel A} {Y : HasEquivRel B} : HasEquivRel (A * B).
Proof.
  intros [x0 y0] [x1 y1].
  apply (x0 == x1 /\ y0 == y1). Defined.

#[export] Instance prod_is_equiv (A B : Type)
  {X : HasEquivRel A} {Y : HasEquivRel B} `{!IsEquiv X} `{IsEquiv Y} :
  IsEquiv (prod_has_equiv_rel (A := A) (B := B)).
Proof.
  unfold prod_has_equiv_rel. split.
  - intros [x y]. split.
    + reflexivity.
    + reflexivity.
  - intros [x0 y0] [x1 y1] [a b]. split.
    + symmetry. apply a.
    + symmetry. apply b.
  - intros [x0 y0] [x1 y1] [x2 y2] [a0 b0] [a1 b1]. split.
    + transitivity x1.
      * apply a0.
      * apply a1.
    + transitivity y1.
      * apply b0.
      * apply b1. Qed.

#[export] Instance option_has_equiv_rel (A : Type) {X : HasEquivRel A} :
  HasEquivRel (option A).
Proof.
  intros [x |] [y |].
  - apply (x == y).
  - apply False.
  - apply False.
  - apply True. Defined.

#[export] Instance option_is_equiv (A : Type)
  {X : HasEquivRel A} `{!IsEquiv X} :
  IsEquiv option_has_equiv_rel.
Proof.
  unfold option_has_equiv_rel. split.
  - intros [x |].
    + reflexivity.
    + auto.
  - intros [x0 |] [x1 |].
    + intros a. symmetry. apply a.
    + intros [].
    + intros [].
    + intros a. apply a.
  - intros [x0 |] [x1 |] [x2 |].
    + intros a0 a1. transitivity x1.
      * apply a0.
      * apply a1.
    + intros a0 [].
    + intros [] [].
    + intros [] a1.
    + intros [] a1.
    + intros [] [].
    + intros a0 [].
    + intros a0 a1. auto. Qed.

#[export] Instance N_has_equiv_rel : HasEquivRel N := eq.
#[export] Instance N_has_equiv_dec : HasEquivDec N := N.eq_dec.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (d : forall x y : A, {X x y} + {~ X x y}) (a : list A) `{!IsEquiv X}.

#[local] Instance has_equiv_rel : HasEquivRel A := X.
#[local] Instance has_equiv_dec : HasEquivDec A := d.
#[local] Instance has_enum : HasEnum A := a.

Ltac notations f := progress (
  f X (equiv_rel (A := A));
  f d (equiv_dec (A := A));
  f a (enum A)).

(** TODO Prove the equivalence of these definitions. *)

#[export] Instance listing_is_size_length
  `{!IsListing X a} : IsSize X (N.of_nat (length a)).
Proof with notations enabled.
  exists encode, decode... split.
  - intros [p t]. apply encode_elim.
    + clear p t. intros p t u _. exfalso.
      rewrite u in t. unfold length, N.of_nat in t. lia.
    + clear p t. intros p t x b u _. rewrite index_nth.
      * unfold snd.
        remember (nth (N.to_nat p) (x :: b) x) as k eqn : ek.
        revert t u ek.
        apply decode_elim.
        -- clear k. intros y q vf _ t vt ve.
           pose proof vf as vf'.
           apply (Nfind_some y x (enum A)) in vf'.
           subst y. destruct vf' as [h0 [h1 v]].
           rewrite Nth_ref in v. simp Nth in v. rewrite <- vt in v.
           (** Need to know indices match due to no duplicates. *)
           assert (m' : q = p).
           { apply nth_inversion in v. lia. rewrite N_length_ref in h1.
             unfold Ref'.N_length in h1. lia. lia. }
           match goal with
           | |- (?p; ?a) = (?q; ?b) =>
             apply (eq_exist_curried
             (P := fun p => p < N.of_nat (length (enum A)))
             (u1 := p) (v1 := q) (u2 := a) (v2 := b) m')
           end. apply irrel.
        -- clear k. intros y vf _ t vt ve. exfalso.
           apply Nfind_none in vf.
           ++ contradiction.
           ++ pose proof full y as fz. apply Exists_IsIn in fz.
              destruct fz as [z [i e]].
              pose proof Proper_IsIn z y (enum A) as w. apply w.
              symmetry. apply e. apply i.
      * rewrite u in t. lia.
  - intros x. apply decode_elim.
    + clear x. intros x n s _.
      remember (n; decode_obligations_obligation_1 x s) as t eqn : et.
      revert et.
      apply encode_elim.
      * clear t. intros p t u _ _. exfalso. rewrite u in t. cbn in t. lia.
      * clear t. intros p t z c u _ et. inversion et; subst p.
        rewrite index_nth.
        -- unfold snd. clear et.
           rewrite <- u.
           apply (Nfind_some x z) in s.
           destruct s as [ix [i e]].
           rewrite Nth_ref in e. apply e.
        -- rewrite <- u. lia.
    + clear x. intros x s _. exfalso.
      apply Nfind_none in s. contradiction.
      pose proof full x as fz. apply Exists_IsIn in fz.
      destruct fz as [z [i e]].
      pose proof Proper_IsIn z x (enum A) as w. apply w.
      symmetry. apply e. apply i. Qed.

#[local] Instance size_length_is_listing
  `{!IsSize X (N.of_nat (length a))} : IsListing X a.
Proof with notations enabled.
  split...
  - intros x. induction (enum A) as [| y b s].
    + exfalso. pose proof size_is_equiv_types as t.
      pose proof equiv_types _ _ _ _ (IsEquivTypes := t) as u.
      destruct u as [f [g v]].
      pose proof g x as w.
      destruct w as [z W].
      simpl in W. lia.
    + apply Exists_cons. destruct (dec (x == y)) as [j | j].
      * left. auto.
      * right. pose proof size_is_equiv_types as t.
        pose proof equiv_types _ _ _ _ (IsEquivTypes := t) as u.
        destruct u as [f [g v]].
        apply s. hnf. Admitted.

End Context.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (d : forall x y : A, {X x y} + {~ X x y}) `{!IsEquiv X}.

#[local] Instance has_equiv_rel' : HasEquivRel A := X.
#[local] Instance has_equiv_dec' : HasEquivDec A := d.

#[export] Instance fin_listing_is_fin_size
  `{!IsFinListing X} : IsFinSize X.
Proof.
  destruct fin_listing as [a ?]. exists (N.of_nat (length a)).
  apply listing_is_size_length; eauto || typeclasses eauto. Qed.

Equations N_seq_sig (n : N) : list {p : N | p < n} :=
  N_seq_sig n := map (fun p : N => (p; _)) (N_seq 0 n).
Next Obligation. intros n p. cbv beta. Admitted.

#[local] Instance fin_size_is_fin_listing
  `{!IsFinSize X} : IsFinListing X.
Proof.
  destruct fin_size as [n s]. pose proof s as t.
  destruct t as [f [g ?]]. exists (map f (N_seq_sig n)).
  apply size_length_is_listing; try eauto || typeclasses eauto.
  rewrite map_length. unfold N_seq_sig.
  rewrite map_length. rewrite N_seq_ref. unfold Ref'.N_seq.
  rewrite map_length. rewrite seq_length. rewrite N2Nat.id.
  typeclasses eauto. Qed.

End Context.
