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

Equations encode_nondep (x : A) (p : N) : A :=
  encode_nondep x p := snd (nth (N.to_nat p) (index (enum A)) (0, x)).

Equations encode (s : {p : N | p < N.of_nat (length (enum A))}) : A :=
  encode (p; t) with inspect (enum A) := {
    | [] eqn : _ => _
    | x :: b eqn : _ => snd (nth (N.to_nat p) (index b) (0, x))
  }.
Next Obligation with notations enabled.
  cbv beta...
  intros p t u. rewrite u in t. unfold length, N.of_nat in t. lia. Qed.

Equations matching (x : A) (s : N * A) : bool :=
  matching x (_, y) := is_left (equiv_dec x y).

Equations decode_nondep (x : A) : N :=
  decode_nondep x with find (matching x) (index (enum A)) := {
    | Some (p, _) => p
    | None => 0
  }.

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
  - unfold matching in t. destruct (equiv_dec x y) as [m | m].
    + discriminate.
    + auto.
  - rewrite <- (Nat2N.id n) in q. rewrite <- q. rewrite <- index_nth.
    + apply nth_In. rewrite index_length. lia.
    + lia. Qed.

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

Lemma encode_indep (x : A) (s : {p : N | p < N.of_nat (length (enum A))}) :
  encode s = encode_nondep x (proj1_sig s).
Proof with notations enabled.
  destruct s as [p t]... unfold proj1_sig. revert t. apply encode_nondep_elim.
  clear x p. intros x p t. set (s := (p; t)). change p with (proj1_sig s).
  clearbody s. clear p t. revert x. apply encode_elim.
  - clear s. intros p t u u' y. exfalso.
    rewrite u in t. unfold N.of_nat, length in t. lia.
  - clear s. intros p t x b u u' y. unfold proj1_sig.
    rewrite u in t. rewrite u. clear u u'.
    (** This is impossible. *) Abort.

Lemma decode_indep `{!IsFull X a} (x : A) :
  proj1_sig (decode x) = decode_nondep x.
Proof with notations enabled.
  apply (decode_nondep_elim
  (P := fun (x : A) (p : N) => proj1_sig (decode x) = p))...
  - clear x. intros x p y u. revert p y u. apply decode_elim.
    + clear x. intros x p y u u' q z v. unfold proj1_sig.
      rewrite u in v. depelim v. reflexivity.
    + clear x. intros x u u' p y v. exfalso.
      rewrite u in v. depelim v.
  - clear x. intros x u. revert u. apply decode_elim.
    + clear x. intros x p y u u' v. exfalso.
      rewrite u in v. depelim v.
    + clear x. intros x u u' v. exfalso.
      pose proof full x as w. apply Exists_exists in w.
      destruct w as [y [wI wX]].
      assert (indexof : forall (A : Type) (l : list A) (x : A), N) by admit.
      set (n := indexof _ (enum A) y).
      apply (fun hole =>
      find_none (matching x) (index (enum A)) hole (n, y)) in v.
      unfold matching in v. destruct (equiv_dec x y); discriminate || auto.
      subst n. Admitted.

(** TODO Prove the equivalence of these definitions. *)

#[export] Instance listing_is_size_length
  `{!IsListing X a} : IsSize X (N.of_nat (length a)).
Proof with notations enabled.
  exists encode, decode... split.
  - intros [p t]. apply encode_elim.
    + clear p t. intros p t u _. exfalso.
      rewrite u in t. unfold length, N.of_nat in t. lia.
    + clear p t. intros p t x b u _. rewrite index_nth. unfold snd.
      remember (nth (N.to_nat p) b x) as k eqn : ek.
      revert t u ek.
      apply decode_elim.
      * clear k. intros y q z vf _ t vt ve.
        pose proof vf as u'. apply find_some in u'. destruct u' as [v w].
        unfold matching in w. unfold has_equiv_dec in w. (* ?? *)
        destruct (d y z) as [m | m].
        -- clear w. subst y.
          apply (In_nth (index (enum A)) _ (N.of_nat 0, x)) in v.
          destruct v as [n [r k]].
          rewrite <- (Nat2N.id n) in k. rewrite index_nth in k.
          rewrite (Nat2N.id n) in k.
          inversion k as [[i j]]. clear k. subst q z.
          pose proof vf as vg. rewrite vt in *. clear vt.
          admit.
          admit.
        -- admit.
      * admit.
      * admit.
  - admit. Abort.

#[export] Instance fin_listing_is_fin_size
  `{!IsFinListing X} : IsFinSize X.
Proof.
  exists (N.of_nat (length a)).
  hnf. induction a as [| x c t].
  - pose proof IsNoDup_nil X as e. exfalso. eapply Exists_nil. eapply full.
  - epose proof IsNoDup_cons x as e.
    epose proof fun y => proj1 (Exists_cons _ x _) (full y) as b'.
    assert (y := x).
    specialize (b' y). destruct b' as [u | u].
    eexists. hnf. Abort.

End Context.
