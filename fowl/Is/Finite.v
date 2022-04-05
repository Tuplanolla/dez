(** * Finiteness *)

From Coq Require Import
  Lia Lists.List Logic.FinFun NArith.NArith.
From DEZ.Has Require Export
  EquivalenceRelations Decisions Enumerations.
From DEZ.Is Require Export
  Isomorphic.
From DEZ.Justifies Require Export
  ProductTheorems NTheorems.

Import ListNotations.

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

Equations index (a : list A) : list (N * A) :=
  index a := combine (N.seq 0 (length a)) a.

#[export] Instance index_has_enum
  {a : HasEnum A} : HasEnum (N * A) := index (enum A).

Equations index_def (a : list A) : list (N * A) :=
  index_def [] := [];
  index_def (x :: b) := (0, x) :: map (prod_bimap N.succ id) (index_def b).

#[export] Instance index_def_has_enum
  {a : HasEnum A} : HasEnum (N * A) := index_def (enum A).

End Context.

Section Context.

Context (A : Type) (X : A -> A -> Prop) {d : @HasEquivDec A X}.

Definition f (a : list A) : {p : N | p < N.of_nat (length a)} -> A.
Proof.
  intros [p s]. destruct a as [| x a].
  - unfold length, N.of_nat in s. lia.
  - apply (snd (nth (N.to_nat p) (index a) (0, x))). Defined.

Axiom admit : forall A : Prop, A.

Definition g (a : list A) : A -> {p : N | p < N.of_nat (length a)}.
Proof.
  intros x.
  set (F := fun s : N * A => if d (snd s) x then true else false).
  set (z := find F (index a)).
  pose proof find_none F (index a) as v.
  pose proof find_some F (index a) as w.
  destruct z as [[n y] |] eqn : e.
  - subst z. clear v. specialize (w _ e). clear e. exists n. apply admit.
  - subst z. clear w. specialize (v e). exists 0. apply admit. Defined.

#[export] Instance listing_is_size_length (a : list A)
  `{!IsListing X a} : IsSize X (N.of_nat (length a)).
Proof.
  hnf. exists (f a), (g a). split. intros [n s]. induction a as [| x c t].
  - cbn in s; lia.
  - cbn in s. cbn. Abort.

#[export] Instance fin_listing_is_fin_size `{!IsFinListing X} : IsFinSize X.
Proof.
  destruct fin_listing as [a s]. exists (N.of_nat (length a)).
  hnf. revert s. induction a as [| x c t]; intros b.
  - pose proof IsNoDup_nil X as e. exfalso. eapply Exists_nil. apply full.
  - epose proof IsNoDup_cons x as e. hnf in b.
    pose proof fun y => proj1 (Exists_cons _ x _) (full y) as b'.
    assert (y := x).
    specialize (b' y). destruct b' as [u | u].
    eexists. hnf. eexists. esplit. Abort.

End Context.
