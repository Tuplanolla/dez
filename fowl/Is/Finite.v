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

Equations nfind_from (n : nat) (x : A) (a : list A) : option nat :=
  nfind_from _ _ [] := None;
  nfind_from n x (y :: b) with dec (x == y) := {
    | left _ := Some n
    | right _ := nfind_from (S n) x b
  }.

Equations nfind (x : A) (a : list A) : option nat :=
  nfind := nfind_from 0.

Equations matching (x : A) (s : N * A) : bool :=
  matching x (_, y) := is_left (dec (x == y)).

Equations decode (x : A) : {p : N | p < N.of_nat (length (enum A))} :=
  decode x with inspect (find (matching x) (index (enum A))) := {
    | Some (p, _) eqn : _ => (p; _)
    | None eqn : _ => _
  }.
Next Obligation with notations enabled.
  cbv beta...
  intros x p y t. apply find_some in t. destruct t as [u v].
  apply index_In in u. lia. Qed.
Next Obligation with notations enabled.
  cbv beta...
  intros x t. exfalso.
  pose proof full x as u. apply Exists_exists in u. destruct u as [y [v w]].
  apply (In_nth (enum A) y x) in v. destruct v as [n [r q]].
  apply (fun p : find (matching x) (index (enum A)) = None =>
  find_none _ _ p (N.of_nat n, y)) in t.
  - unfold matching in t. destruct (dec (x == y)) as [m | m].
    + discriminate.
    + auto.
  - rewrite <- (Nat2N.id n) in q. rewrite <- q. rewrite <- index_nth.
    + apply nth_In. rewrite index_length. lia.
    + lia. Qed.

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

Context (A : Type) {X : HasEquivRel A} {d : HasEquivDec A} {a : HasEnum A}
  `{!IsEquiv X} `{!IsFull X a} `{!IsNoDup X a}.

Ltac notations f := progress (
  f X (equiv_rel (A := A));
  f d (equiv_dec (A := A));
  f a (enum A)).

(** TODO These are extra dubious! *)

Lemma find_matching_index_from (x : A) (k : N) :
  exists n : N, n < N.of_nat (length (enum A)) /\
  find (matching x) (index_from k (enum A)) == Some (k + n, x).
Proof with notations enabled.
  idtac... pose proof full x as s'. clear IsFull0 IsNoDup0.
  revert k s'. induction (enum A) as [| y b s]; intros k s'.
  - exfalso. rename s' into s. apply Exists_exists in s.
    destruct s as [y [[] v]].
  - destruct (dec (x == y)) as [t | t] eqn : ed.
    + exists 0. split.
      * simpl. lia.
      * simp index_from. simpl find. rewrite ed. split.
        -- rewrite N.add_0_r. reflexivity.
        -- rewrite t. reflexivity.
    + inversion s'; subst.
      * congruence.
      * specialize (s (N.succ k) H0). destruct s as [n [L R]].
        exists (N.succ n). split.
        -- simpl. lia.
        -- simpl. rewrite ed. simpl. eapply trans.
          ++ apply R.
          ++ replace (N.succ k + n) with (k + N.succ n) by lia.
            reflexivity. Qed.

Lemma find_matching_index (x : A) :
  exists n : N, n < N.of_nat (length (enum A)) /\
  find (matching x) (index (enum A)) == Some (n, x).
Proof with notations enabled. apply find_matching_index_from. Qed.

Lemma find_matching_index_from' (x y : A) (k n : N)
  (sn : n < N.of_nat (length (enum A)))
  (sx : nth (N.to_nat n) (enum A) y == x) :
  find (matching x) (index_from k (enum A)) == Some (k + n, x).
Proof with notations enabled.
  idtac... pose proof full x as sf. clear IsFull0 IsNoDup0.
  revert k sn sx sf. induction (enum A) as [| z b s]; intros k sn sx sf.
  - exfalso. apply Exists_exists in sf.
    destruct sf as [z [[] v]].
  - destruct (dec (x == z)) as [t | t] eqn : ed.
    + simpl. rewrite ed. simpl. Admitted.

Lemma find_matching_index' (x y : A) (n : N)
  (sn : n < N.of_nat (length (enum A)))
  (sx : nth (N.to_nat n) (enum A) y == x) :
  find (matching x) (index (enum A)) == Some (n, x).
Proof with notations enabled.
  rewrite <- (N.add_0_l n). eapply find_matching_index_from'; eauto. Qed.

Lemma need_this (n : N) (x y : A)
  (s : n < N.of_nat (length (enum A)))
  (t : nth (N.to_nat n) (enum A) y == x) :
  find (matching x) (index (enum A)) == Some (n, x).
Proof.
  pose proof find_matching_index x as u.
  destruct u as [p [v w]].
  rewrite w. Admitted.

Lemma need_this_too (n : N) (x y : A)
  (s : find (matching x) (index (enum A)) == Some (n, x)) :
  nth (N.to_nat n) (enum A) y == x.
Proof. Admitted.

Lemma need_this_as_well (n : N) (x y : A)
  (s : find (matching x) (index (enum A)) = None) : 0.
Proof. Admitted.

End Context.

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
        --- intros y q z vf _ t vt ve.
            assert (vf' : find (matching y) (index (enum A)) == Some (q, z)).
            { rewrite vf. reflexivity. }
            subst y. rewrite <- vt in vf'.
            rewrite (find_matching_index' _ x p) in vf'.
            inversion vf' as [m w].
            assert (m' : q = p) by (symmetry; apply m).
            match goal with
            | |- (?p; ?a) = (?q; ?b) =>
              apply (eq_exist_curried
              (P := fun p => p < N.of_nat (length (enum A)))
              (u1 := p) (v1 := q) (u2 := a) (v2 := b) m')
            end. apply irrel.
            apply t.
            reflexivity.
        --- clear k. intros y vf _ t vt ve. exfalso.
            assert (vf' : find (matching y) (index (enum A)) == None).
            { rewrite vf. reflexivity. }
            subst y. rewrite <- vt in vf'.
            rewrite (find_matching_index' _ x p) in vf'.
            inversion vf'.
            apply t.
            reflexivity.
      * rewrite u in t. lia.
  - intros x. apply decode_elim.
    + clear x. intros x n y s _.
      remember (n; decode_obligations_obligation_1 x s) as t eqn : et.
      revert et.
      apply encode_elim.
      * clear t. intros p t u _ _. exfalso. rewrite u in t. cbn in t. lia.
      * clear t. intros p t z c u _ et. inversion et; subst p.
        rewrite index_nth.
        --- unfold snd. clear et.
            rewrite <- u.
            admit.
        --- rewrite <- u. lia.
    + clear x. intros x s _. exfalso.
      admit. Admitted.

#[local] Instance size_length_is_listing
  `{!IsSize X (N.of_nat (length a))} : IsListing X a.
Proof with notations enabled.
  split...
  - intros x. induction (enum A) as [| y b s].
    + exfalso. pose proof size_is_equiv_types as t.
      pose proof equiv_types _ _ _ _ (IsEquivTypes := t) as u.
      destruct u as [f [g v]].
      pose proof g x as w.
      destruct w as [y W].
      simpl in W. lia.
    + apply Exists_cons. destruct (dec (x == y)) as [t | t].
      * left. auto.
      * right. apply s. Admitted.

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

Equations N_seq (n : N) : list {p : N | p < n} :=
  N_seq n := map (fun p : nat => (N.of_nat p; _)) (seq 0 (N.to_nat n)).
Next Obligation. intros n p. cbv beta. Admitted.

#[local] Instance fin_size_is_fin_listing
  `{!IsFinSize X} : IsFinListing X.
Proof.
  destruct fin_size as [n s]. pose proof s as t.
  destruct t as [f [g ?]]. exists (map f (N_seq n)).
  apply size_length_is_listing; try eauto || typeclasses eauto.
  rewrite map_length. unfold N_seq.
  rewrite map_length. rewrite seq_length. rewrite N2Nat.id.
  typeclasses eauto. Qed.

End Context.
