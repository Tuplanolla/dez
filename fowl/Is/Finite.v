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

Import ListNotations.

#[local] Open Scope core_scope.
#[local] Open Scope N_scope.

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

(** This is simpler to prove things about. *)

Equations index (a : list A) : list (N * A) :=
  index a := combine (map N.of_nat (seq 0 (length a))) a.

#[export] Instance index_has_enum
  {a : HasEnum A} : HasEnum (N * A) := index (enum A).

Lemma index_length (a : list A) : length (index a) = length a.
Proof.
  unfold index.
  rewrite combine_length. rewrite map_length. rewrite seq_length.
  rewrite Min.min_idempotent. reflexivity. Qed.

Lemma index_ed (a : list A) (p : N) (x : A) (s : In (p, x) (index a)) :
  p < N.of_nat (length a).
Proof.
  unfold index in s. apply in_combine_l in s. apply (in_map N.to_nat) in s.
  rewrite map_map in s. rewrite (map_ext _ id) in s.
  - rewrite map_id in s. apply in_seq in s. lia.
  - intros n. rewrite Nat2N.id. reflexivity. Qed.

End Context.

Module Better.

Section Context.

Context (A : Type).

(** This is computationally better-behaved. *)

Fail Fail Equations index_fix (n : N) (a : list A) : list (N * A) :=
  index_fix _ [] := [];
  index_fix n (x :: b) := (n, x) :: index_fix (N.succ n) b.

Equations index (a : list A) : list (N * A) :=
  index := index_fix 0 where
  index_fix (n : N) (a : list A) : list (N * A) :=
    index_fix _ [] := [];
    index_fix n (x :: b) := (n, x) :: index_fix (N.succ n) b.

#[export] Instance index_fix_has_enum
  {a : HasEnum A} : HasEnum (N * A) := index (enum A).

End Context.

End Better.

Lemma proj1_sig_inj (A : Type) (P : A -> Prop)
  (a b : {x : A | P x}) (s : proj1_sig a = proj1_sig b) : a = b.
Proof. Admitted.

Section Context.

Context (A : Type) {X : HasEquivRel A} {d : HasEquivDec A} {a : HasEnum A}
  `{!IsEquiv X} `{!IsListing X a}.

Ltac note := progress (
  denote X with (equiv_rel (A := A));
  denote d with (equiv_dec (A := A));
  denote a with (enum A)).

#[local] Open Scope sig_scope.

Equations encode (s : {p : N | p < N.of_nat (length (enum A))}) : A :=
  encode (p; t) with (enum A; eq_refl) := {
    | ([]; _) := _
    | (x :: b; _) := snd (nth (N.to_nat p) (index b) (0, x))
  }.
Next Obligation.
  intros p t u. cbv beta in t. rewrite u in t.
  unfold length, N.of_nat in t. lia. Qed.

Definition is_left (A B : Prop) (x : {A} + {B}) : bool :=
  if x then true else false.

Equations matching (x : A) (s : N * A) : bool :=
  matching x (_, y) := is_left (d x y).

Equations decode (x : A) : {p : N | p < N.of_nat (length (enum A))} :=
  decode x with (find (matching x) (index (enum A)); eq_refl) := {
    | (Some (p, y); _) := (p; _)
    | (None; _) := _
  }.
Next Obligation with note.
  intros x p y t...
  apply find_some in t. destruct t as [u v]. apply index_ed in u. lia. Qed.
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

#[export] Instance listing_is_size_length :
  IsSize X (N.of_nat (length (enum A))).
Proof with note.
  hnf. exists encode, decode. split.
  - intros [p t]. apply_funelim (encode (p; t)).
    clear p t. intros p t e e'. clear e'. exfalso. rewrite e in t. cbn in t. lia.
    clear p t. intros p t x b e e'. clear e'.
    apply_funelim (decode (snd (nth (N.to_nat p) (index b) (0, x)))).
    clear x b e. intros x q y e e'. clear e'.
    apply proj1_sig_inj. unfold proj1_sig.
    all: admit.
  - intros x... apply_funelim (decode x). Abort.

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
