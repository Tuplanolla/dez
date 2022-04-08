(** * Finiteness *)

From Coq Require Import
  Lia Lists.List Logic.FinFun NArith.NArith.
From DEZ.Has Require Export
  EquivalenceRelations Decisions Enumerations.
From DEZ.Is Require Export
  Isomorphic Extensional Truncated.
From DEZ.Justifies Require Export
  OptionTheorems ProductTheorems NTheorems.
From DEZ.Provides Require Import
  TypeclassTactics.
From DEZ.Supports Require Import
  EquivalenceNotations.

Equations is_left (A B : Prop) (a : {A} + {B}) : bool :=
  is_left (left _) := true;
  is_left (right _) := false.

Import ListNotations.

#[local] Open Scope core_scope.
#[local] Open Scope N_scope.
#[local] Open Scope sig_scope.

(** ** Unsorted Enumeration of a Type *)

(** This is a generalization of [Full]. *)

Class IsFull (A : Type) (X : A -> A -> Prop) (a : list A) : Prop :=
  full (x : A) : Exists (X x) a.

(** ** Uniqueness of a Listing *)

(** This is a generalization of [NoDup]. *)

Inductive IsNoDup (A : Type) (X : A -> A -> Prop) : list A -> Prop :=
  | IsNoDup_nil : IsNoDup X []
  | IsNoDup_cons (x : A) (a : list A) (s : ~ Exists (X x) a)
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

Class IsFinListing (A : Type) (X : A -> A -> Prop) : Prop :=
  fin_listing : exists a : list A, IsListing X a.

(** ** Size of a Type *)

Class IsSize (A : Type) (X : A -> A -> Prop) (n : N) : Prop :=
  size_is_equiv_types :> IsEquivTypes (A := {p : N | p < n}) _=_ X.

(** ** Finiteness in Terms of Counting *)

Class IsFinSize (A : Type) (X : A -> A -> Prop) : Prop :=
  fin_size : exists n : N, IsSize X n.

(** TODO Prove the equivalence of these definitions. *)

Section Context.

Context (A : Type) {X : HasEquivRel A} {d : HasEquivDec A} `{!IsFinListing X}.

End Context.

Section Context.

Context (A : Type).

(** This is simpler to use in proofs. *)

Equations index (a : list A) : list (N * A) :=
  index a := combine (map N.of_nat (seq 0 (length a))) a.

#[export] Instance index_has_enum
  {a : HasEnum A} : HasEnum (N * A) := index (enum A).

Lemma index_length (a : list A) : length (index a) = length a.
Proof.
  unfold index.
  rewrite combine_length. rewrite map_length. rewrite seq_length.
  rewrite Min.min_idempotent. reflexivity. Qed.

Lemma index_In (a : list A) (p : N) (x : A) (s : In (p, x) (index a)) :
  p < N.of_nat (length a).
Proof.
  unfold index in s. apply in_combine_l in s. apply (in_map N.to_nat) in s.
  rewrite map_map in s. rewrite (map_ext _ id) in s.
  - rewrite map_id in s. apply in_seq in s. lia.
  - intros n. rewrite Nat2N.id. reflexivity. Qed.

End Context.

Module Faster.

Section Context.

Context (A : Type).

(** This is faster to use in computations. *)

Equations index (a : list A) : list (N * A) :=
  index := index_fix 0 where
  index_fix (n : N) (a : list A) : list (N * A) :=
  index_fix _ [] := [];
  index_fix n (x :: b) := (n, x) :: index_fix (N.succ n) b.

#[export] Instance index_fix_has_enum
  {a : HasEnum A} : HasEnum (N * A) := index (enum A).

End Context.

End Faster.

Section Context.

Context (A : Type) {X : HasEquivRel A} {d : HasEquivDec A} {a : HasEnum A}
  `{!IsEquiv X} `{!IsListing X a}.

Ltac note := progress (
  denote X with (equiv_rel (A := A));
  denote d with (equiv_dec (A := A));
  denote a with (enum A)).

Equations encode (s : {p : N | p < N.of_nat (length (enum A))}) : A :=
  encode (p; t) with (enum A; eq_refl) := {
    | ([]; _) => _
    | (x :: b; _) => snd (nth (N.to_nat p) (index b) (0, x))
  }.
Next Obligation.
  intros p t u. cbv beta in t. rewrite u in t.
  unfold length, N.of_nat in t. lia. Qed.

Equations encode_without_inspect (s : {p : N | p < N.of_nat (length a)}) : A :=
  encode_without_inspect := encode_without_inspect_fix (enum A) where
  encode_without_inspect_fix (a : list A) (s : {p : N | p < N.of_nat (length a)}) : A :=
  encode_without_inspect_fix [] _ := _;
  encode_without_inspect_fix (x :: b) (p; _) := snd (nth (N.to_nat p) (index b) (0, x)).
Next Obligation. unfold length, N.of_nat; intros []; lia. Qed.

Equations matching (x : A) (s : N * A) : bool :=
  matching x (_, y) := is_left (d x y).

Equations decode (x : A) : {p : N | p < N.of_nat (length (enum A))} :=
  decode x with (find (matching x) (index (enum A)); eq_refl) := {
    | (Some (p, y); _) => (p; _)
    | (None; _) => _
  }.
Next Obligation with note.
  intros x p y t...
  apply find_some in t. destruct t as [u v]. apply index_In in u. lia. Qed.
Next Obligation with note.
  intros x t... exfalso.
  pose proof full x as u.
  apply Exists_exists in u.
  destruct u as [y [v w]].
  apply (In_nth a y x) in v. destruct v as [n [q r]].
  apply (fun z => find_none _ (index (enum A)) z (N.of_nat n, y)) in t.
  cbn in t. unfold is_left in t. destruct (d x y) as [m | m].
  congruence. apply m, w...
  assert (what : (N.of_nat n, y) = nth n (index (enum A)) (N.of_nat 0, x)).
  { unfold index. rewrite combine_nth.
    - f_equal.
      + rewrite map_nth. f_equal. rewrite seq_nth... lia. lia.
      + rewrite r. reflexivity.
    - rewrite map_length. rewrite seq_length. reflexivity. }
  rewrite what.
  apply nth_In.
  rewrite index_length... lia. Qed.

Equations decode_fst_without_inspect (x : A) : N :=
  decode_fst_without_inspect x with find (matching x) (index (enum A)) := {
    | Some (p, y) => p
    | None => 0
  }.

Lemma decode_snd_without_inspect (x : A) :
  decode_fst_without_inspect x < N.of_nat (length (enum A)).
Proof with note.
  apply_funelim (decode_fst_without_inspect x). all: clear x.
  ----
  intros x p y t...
  apply find_some in t. destruct t as [u v]. apply index_In in u. lia.
  ----
  intros x t... exfalso.
  pose proof full x as u.
  apply Exists_exists in u.
  destruct u as [y [v w]].
  apply (In_nth a y x) in v. destruct v as [n [q r]].
  apply (fun z => find_none _ (index (enum A)) z (N.of_nat n, y)) in t.
  cbn in t. unfold is_left in t. destruct (d x y) as [m | m].
  congruence. apply m, w...
  assert (what : (N.of_nat n, y) = nth n (index (enum A)) (N.of_nat 0, x)).
  { unfold index. rewrite combine_nth.
    - f_equal.
      + rewrite map_nth. f_equal. rewrite seq_nth... lia. lia.
      + rewrite r. reflexivity.
    - rewrite map_length. rewrite seq_length. reflexivity. }
  rewrite what.
  apply nth_In.
  rewrite index_length... lia. Qed.

Equations decode_without_inspect (x : A) : {p : N | p < N.of_nat (length (enum A))} :=
  decode_without_inspect x := (decode_fst_without_inspect x; decode_snd_without_inspect x).

#[export] Instance listing_is_size_length :
  IsSize X (N.of_nat (length (enum A))).
Proof with note.
  hnf. exists encode, decode. split...
  - intros [p t]. unfold encode, decode.
    unfold enum in *. Fail induction a. admit.
  - intros x. apply (decode_elim
      (fun (x : A) (s : {p : N | p < N.of_nat (length (enum A))}) =>
      encode s == x)).
    clear x. intros x p y e _.
    remember (p; decode_obligations_obligation_1 x e) as G eqn : eg.
    apply encode_elim. admit. intros q t z b e' _.
    unfold enum in *. destruct G as [p' t']. depelim eg.
    assert (i : IsListing _==_ a) by auto.
    rewrite e' in e, t, i. clear e'.
    unfold matching. cbn in *.
    destruct (d x z) as [w | w] eqn : ew. cbn in *. rewrite w.
    depelim e. rewrite combine_nth. unfold snd.
    2: rewrite map_length. 2: rewrite seq_length. 2: reflexivity.
    pose proof full y as fy.
    apply Exists_nth in fy. destruct fy as [j [def [ly ry]]]. Abort.

#[export] Instance listing_is_size_length :
  IsSize X (N.of_nat (length (enum A))).
Proof with note.
  hnf. exists encode_without_inspect, decode_without_inspect. split.
  - intros [p t]. unfold encode_without_inspect, decode_without_inspect.
    apply eq_sig_hprop. admit. unfold proj1_sig.
    unfold decode_fst_without_inspect,
    decode_fst_without_inspect_clause_1,
    encode_without_inspect_clause_1_encode_without_inspect_fix.
    unfold enum in *. destruct a as [| x c].
    cbn in t; lia. Abort.

#[export] Instance fin_listing_is_fin_size `{!IsFinListing X} : IsFinSize X.
Proof.
  exists (N.of_nat (length a)).
  hnf. induction a as [| x c t].
  - pose proof IsNoDup_nil X as e. exfalso. eapply Exists_nil. apply full.
  - epose proof IsNoDup_cons x as e.
    pose proof fun y => proj1 (Exists_cons _ x _) (full y) as b'.
    assert (y := x).
    specialize (b' y). destruct b' as [u | u].
    eexists. hnf. Abort.

End Context.
