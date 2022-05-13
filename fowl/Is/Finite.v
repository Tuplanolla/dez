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

Notation "'_::_'" := cons : list_scope.
Notation "x '::' a" := (cons x a) : list_scope.

Lemma map_bimap_combine (A B C D : Type)
  (f : A -> C) (g : B -> D) (a : list A) (b : list B) :
  map (prod_bimap f g) (combine a b) = combine (map f a) (map g b).
Proof.
  revert b. induction a as [| x c s]; intros [| y d].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. f_equal. apply s. Qed.

Lemma Forall2_dec (A B : Type) (P : A -> B -> Prop)
  (d : forall (x : A) (y : B), {P x y} + {~ P x y})
  (a : list A) (b : list B) :
  {Forall2 P a b} + {~ Forall2 P a b}.
Proof.
  destruct (dec (length a = length b)) as [s | s].
  -- revert b s. induction a as [| x c t]; intros [| y e] s.
  - left. apply Forall2_nil.
  - discriminate.
  - discriminate.
  - pose proof d x y as d'.
    inversion s as [s']. pose proof t _ s' as t'. clear s'.
    destruct d' as [d' | fd'], t' as [t' | ft'].
    + left. apply Forall2_cons.
      * apply d'.
      * apply t'.
    + right. intros cd. inversion_clear cd. contradiction.
    + right. intros cd. inversion_clear cd. contradiction.
    + right. intros cd. inversion_clear cd. contradiction.
  -- revert b s. induction a as [| x c t]; intros [| y e] s.
  - left. apply Forall2_nil.
  - right. intros cd. inversion cd.
  - right. intros cd. inversion cd.
  - simpl length in s.
    apply (PeanoNat.Nat.succ_inj_wd_neg (length c) (length e)) in s.
    pose proof d x y as d'.
    pose proof t _ s as t'. clear s.
    destruct d' as [d' | fd'], t' as [t' | ft'].
    + left. apply Forall2_cons.
      * apply d'.
      * apply t'.
    + right. intros cd. inversion_clear cd. contradiction.
    + right. intros cd. inversion_clear cd. contradiction.
    + right. intros cd. inversion_clear cd. contradiction. Defined.

Section Context.

Context (A : Type).

#[export] Instance list_has_equiv_rel
  {X : HasEquivRel A} : HasEquivRel (list A) :=
  Forall2 X.

#[export] Instance list_has_equiv_dec
  {X : HasEquivRel A} {d : HasEquivDec A} : HasEquivDec (list A) :=
  Forall2_dec d.

#[export] Instance list_is_equiv
  {X : HasEquivRel A} {d : HasEquivDec A} `{!IsEquiv X} : IsEquiv (Forall2 X).
Proof.
  split.
  - intros x. induction x as [| y b s].
    + apply Forall2_nil.
    + apply Forall2_cons.
      * reflexivity.
      * apply s.
  - intros x. induction x as [| z b t]; intros [| w c] s.
    + apply Forall2_nil.
    + inversion s.
    + inversion s.
    + inversion_clear s as [| ? ? ? ? u v]. apply Forall2_cons.
      * symmetry. apply u.
      * apply t. apply v.
  - intros x. induction x as [| z b t]; intros [| w c] [| ww cc] s tt.
    + apply Forall2_nil.
    + inversion tt.
    + inversion s || inversion tt.
    + inversion s.
    + inversion s.
    + inversion s || inversion tt.
    + inversion tt.
    + inversion_clear s as [| ? ? ? ? u v].
      inversion_clear tt as [| ? ? ? ? uu vv]. apply Forall2_cons.
      * etransitivity.
        -- apply u.
        -- apply uu.
      * eapply t.
        -- apply v.
        -- apply vv. Qed.

#[export] Instance cons_Proper {X : HasEquivRel A} :
  IsProper (X ==> Forall2 X ==> Forall2 X) _::_.
Proof.
  intros x y s a b t. apply Forall2_cons.
  - apply s.
  - apply t. Qed.

End Context.

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

Section Context.

Context (A : Type).

Equations nindex_from (n : nat) (a : list A) : list (nat * A) by struct a :=
  nindex_from _ [] := [];
  nindex_from n (x :: b) := (n, x) :: nindex_from (S n) b.

Equations nindex (a : list A) : list (nat * A) :=
  nindex := nindex_from O.

Context {X : HasEquivRel A} {d : HasEquivDec A}.

Equations nfind_error_from (n : nat) (x : A) (a : list A) : option nat :=
  nfind_error_from _ _ [] := None;
  nfind_error_from n x (y :: b) with dec (x == y) := {
    | left _ := Some n
    | right _ := nfind_error_from (S n) x b
  }.

Equations nfind_error (x : A) (a : list A) : option nat :=
  nfind_error := nfind_error_from O.

Equations nfind_from (n : nat) (x : A) (a : list A) (p : nat) : nat :=
  nfind_from _ _ [] p := p;
  nfind_from n x (y :: b) p with dec (x == y) := {
    | left _ := n
    | right _ := nfind_from (S n) x b p
  }.

Equations nfind (x : A) (a : list A) (p : nat) : nat :=
  nfind := nfind_from O.

End Context.

Section Context.

Context (A : Type) {X : HasEquivRel A} {d : HasEquivDec A}.

Lemma nfind_error_nfind (x : A) (a : list A) (n p : nat)
  (s : nfind_error x a = Some n) : nfind x a p = n.
Proof. Admitted.

Lemma nfind_error_nfind' (x : A) (a : list A) (n p : nat)
  (s : (n < length a)%nat) : nfind_error x a = Some (nfind x a p).
Proof. Admitted.

Lemma nfind_error_None (x : A) (a : list A) (n : nat)
  (s : nfind_error x a = None) : (length a <= n)%nat.
Proof. Admitted.

Lemma nfind_error_Some (x : A) (a : list A) (n : nat)
  (s : nfind_error x a <> None) : (n < length a)%nat.
Proof. Admitted.

End Context.

(** This reference implementation is simpler to use in proofs;
    the other implementation is faster to use in computations. *)

Module Ref.

Section Context.

Context (A : Type).

Equations nindex_from (n : nat) (a : list A) : list (nat * A) :=
  nindex_from n a := combine (seq n (length a)) a.

Equations nindex (a : list A) : list (nat * A) :=
  nindex := nindex_from O.

End Context.

Section Context.

Equations N_seq (n p : N) : list N :=
  N_seq n p := map N.of_nat (seq (N.to_nat n) (N.to_nat p)).

Context (A : Type).

Equations N_length (a : list A) : N :=
  N_length a := N.of_nat (length a).

Equations Nth (n : N) (a : list A) (x : A) : A :=
  Nth n := nth (N.to_nat n).

Equations Nindex_from (n : N) (a : list A) : list (N * A) :=
  Nindex_from n a := map (prod_bimap N.of_nat id) (nindex_from (N.to_nat n) a).

Equations Nindex (a : list A) : list (N * A) :=
  Nindex a := map (prod_bimap N.of_nat id) (nindex a).

Context {X : HasEquivRel A} {d : HasEquivDec A}.

Equations Nfind_error_from (n : N) (x : A) (a : list A) : option N :=
  Nfind_error_from n x a := option_map N.of_nat (nfind_error_from (N.to_nat n) x a).

Equations Nfind_error (x : A) (a : list A) : option N :=
  Nfind_error x a := option_map N.of_nat (nfind_error x a).

Equations Nfind_from (n : N) (x : A) (a : list A) (p : N) : N :=
  Nfind_from n x a p := N.of_nat (nfind_from (N.to_nat n) x a (N.to_nat p)).

Equations Nfind (x : A) (a : list A) (p : N) : N :=
  Nfind x a p := N.of_nat (nfind x a (N.to_nat p)).

End Context.

End Ref.

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

Equations Nindex_from (n : N) (a : list A) : list (N * A) by struct a :=
  Nindex_from _ [] := [];
  Nindex_from n (x :: b) := (n, x) :: Nindex_from (N.succ n) b.

Equations Nindex (a : list A) : list (N * A) :=
  Nindex := Nindex_from 0.

Context {X : HasEquivRel A} {d : HasEquivDec A}.

Equations Nfind_error_from (n : N) (x : A) (a : list A) : option N :=
  Nfind_error_from _ _ [] := None;
  Nfind_error_from n x (y :: b) with dec (x == y) := {
    | left _ := Some n
    | right _ := Nfind_error_from (N.succ n) x b
  }.

Equations Nfind_error (x : A) (a : list A) : option N :=
  Nfind_error := Nfind_error_from 0.

Equations Nfind_from (n : N) (x : A) (a : list A) (p : N) : N :=
  Nfind_from _ _ [] p := p;
  Nfind_from n x (y :: b) p with dec (x == y) := {
    | left _ := n
    | right _ := Nfind_from (N.succ n) x b p
  }.

Equations Nfind (x : A) (a : list A) (p : N) : N :=
  Nfind := Nfind_from 0.

End Context.

Lemma nindex_from_ref (A : Type) (n : nat) (a : list A) :
  nindex_from n a = Ref.nindex_from n a.
Proof.
  apply Ref.nindex_from_elim. clear n a. intros n a. apply nindex_from_elim.
  - clear n a. intros n. reflexivity.
  - clear n a. intros n x a s.
    simpl. f_equal. apply s. Qed.

Lemma nindex_ref (A : Type) (a : list A) : nindex a = Ref.nindex a.
Proof. apply Ref.nindex_elim. apply nindex_elim. apply nindex_from_ref. Qed.

Lemma N_length_ref (A : Type) (a : list A) :
  N_length a = Ref.N_length a.
Proof.
  apply Ref.N_length_elim. clear a. intros a. apply N_length_elim.
  - clear a. reflexivity.
  - clear a. intros x b s.
    simpl length. rewrite Nat2N.inj_succ. f_equal. apply s. Qed.

Lemma Nth_ref (A : Type) (n : N) (a : list A) (x : A) :
  Nth n a x = Ref.Nth n a x.
Proof.
  apply Ref.Nth_elim. clear n. intros n. apply Nth_elim.
  - clear x n. intros n x. destruct n as [| p _] using N.peano_ind.
    + reflexivity.
    + rewrite N2Nat.inj_succ. reflexivity.
  - clear x n. intros y n x. reflexivity.
  - clear x n. intros p y b x s.
    rewrite N2Nat.inj_pred in s. destruct (N.to_nat (N.pos p)) as [| q] eqn : t.
    + lia.
    + apply s. Qed.

Lemma N_seq_ref (n p : N) :
  N_seq n p = Ref.N_seq n p.
Proof.
  apply Ref.N_seq_elim. clear n p. intros n p.
  revert n. induction p as [| q s] using N.peano_ind; intros n.
  - reflexivity.
  - rewrite N2Nat.inj_succ. simpl seq. simpl map.
    pose proof s (N.succ n) as s'. rewrite N2Nat.inj_succ in s'.
    rewrite N2Nat.id. rewrite <- N.succ_pos_spec. simp N_seq.
    rewrite N.succ_pos_spec. rewrite N.pred_succ. f_equal. apply s'. Qed.

Lemma Nindex_from_ref (A : Type) (n : N) (a : list A) :
  Nindex_from n a = Ref.Nindex_from n a.
Proof.
  apply Ref.Nindex_from_elim. clear n a. intros n a. apply Nindex_from_elim.
  - clear n a. intros n. reflexivity.
  - clear n a. intros n x a s.
    simpl. rewrite N2Nat.id. f_equal.
    rewrite N2Nat.inj_succ in s. apply s. Qed.

Lemma Nindex_ref (A : Type) (a : list A) : Nindex a = Ref.Nindex a.
Proof. apply Ref.Nindex_elim. apply Nindex_elim. apply Nindex_from_ref. Qed.

Section Context.

Context (A : Type) {X : HasEquivRel A} {d : HasEquivDec A}.

Lemma Nfind_error_from_ref (n : N) (x : A) (a : list A) :
  Nfind_error_from n x a = Ref.Nfind_error_from n x a.
Proof.
  apply Ref.Nfind_error_from_elim. clear n x a. intros n x a.
  revert n x. induction a as [| y b s]; intros n x.
  - reflexivity.
  - destruct (dec (x == y)) as [ex | fx] eqn : ed.
    + simp Nfind_error_from nfind_error_from. rewrite ed. simpl.
      rewrite N2Nat.id. reflexivity.
    + simp Nfind_error_from nfind_error_from. rewrite ed. simpl.
      pose proof s (N.succ n) x as s'. rewrite N2Nat.inj_succ in s'.
      apply s'. Qed.

Lemma Nfind_error_ref (x : A) (a : list A) :
  Nfind_error x a = Ref.Nfind_error x a.
Proof.
  apply Nfind_error_elim. apply Ref.Nfind_error_elim. clear x a. intros x a.
  apply nfind_error_elim. apply Nfind_error_from_ref. Qed.

Lemma Nfind_from_ref (n : N) (x : A) (a : list A) (p : N) :
  Nfind_from n x a p = Ref.Nfind_from n x a p.
Proof.
  apply Ref.Nfind_from_elim. clear n x a p. intros n x a p.
  revert n x p. induction a as [| y b s]; intros n x p.
  - simpl. rewrite N2Nat.id. reflexivity.
  - destruct (dec (x == y)) as [ex | fx] eqn : ed.
    + simp Nfind_from nfind_from. rewrite ed. simpl.
      rewrite N2Nat.id. reflexivity.
    + simp Nfind_from nfind_from. rewrite ed. simpl.
      pose proof s (N.succ n) x as s'. rewrite N2Nat.inj_succ in s'.
      apply s'. Qed.

Lemma Nfind_ref (x : A) (a : list A) (p : N) :
  Nfind x a p = Ref.Nfind x a p.
Proof.
  apply Nfind_elim. apply Ref.Nfind_elim. clear x a p. intros x a p.
  apply nfind_elim. apply Nfind_from_ref. Qed.

End Context.

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

Lemma IsIn_Exists (P : A -> Prop) `{!IsProper (X ==> _<->_) P}
  (a : list A) (s : exists x : A, IsIn x a /\ P x) :
  Exists P a.
Proof.
  destruct s as [x [i t]]. induction a as [| y b u].
  - contradiction.
  - induction i as [v | v].
    + apply Exists_cons. left. rewrite <- v. apply t.
    + apply Exists_cons. right. apply u. apply v. Qed.

Lemma Proper_IsIn (x y : A) (a : list A)
  (s : x == y) (t : IsIn x a) : IsIn y a.
Proof.
  induction a as [| z b u].
  - contradiction.
  - destruct t as [v | v].
    + left. rewrite <- s, <- v. reflexivity.
    + right. apply u. apply v. Qed.

#[export] Instance IsIn_is_proper (a : list A) :
  IsProper (X ==> _<->_) (fun x : A => IsIn x a).
Proof.
  intros x y s. split.
  - intros t. eapply Proper_IsIn. apply s. apply t.
  - intros t. eapply Proper_IsIn. symmetry. apply s. apply t. Qed.

#[export] Instance IsIn_is_proper' (x : A) :
  IsProper (Forall2 X ==> _<->_) (IsIn x).
Proof.
  intros a b s. split.
  - intros t. induction s as [| y z a b s u v].
    + contradiction.
    + destruct t as [w | w].
      * left. etransitivity.
        -- apply w.
        -- apply s.
      * right. auto.
  - intros t. induction s as [| y z a b s u v].
    + contradiction.
    + destruct t as [w | w].
      * left. etransitivity.
        -- apply w.
        -- symmetry. apply s.
      * right. auto. Qed.

Lemma nth_IsIn (n : nat) (a : list A) (y : A) :
  (n < length a)%nat -> IsIn (nth n a y) a.
Proof.
  revert a; induction n as [| p s]; intros a t.
  - destruct a as [| z b]. simpl in t; lia.
    simpl. left. reflexivity.
  - destruct a as [| z b]. simpl in t; lia.
    simpl. right. apply s. simpl in t; lia. Qed.

Lemma Nth_succ (n : N) (y : A) (b : list A) (x : A) :
  Nth (N.succ n) (y :: b) x = Nth n b x.
Proof.
  destruct n as [| p].
  - simp Nth. simpl N.pred. reflexivity.
  - simp Nth. simpl N.pred. rewrite Pos.pred_N_succ. reflexivity. Qed.

Lemma Nfind_error_from_succ (n p : N) (x : A) (a : list A)
  (e : Nfind_error_from n x a = Some p) : Nfind_error_from (N.succ n) x a = Some (N.succ p).
Proof.
  revert e. apply Nfind_error_from_elim.
  - clear n x a. intros n x e.
    discriminate.
  - clear n x a. intros n x y ex b ed e.
    simp Nfind_error_from. rewrite ed. simpl.
    inversion_clear e. reflexivity.
  - clear n x a. intros n x y ex b es ed e.
    simp Nfind_error_from. rewrite ed. simpl.
    apply es. apply e. Qed.

Lemma Nfind_error_from_succ' (n p : N) (x : A) (a : list A)
  (e : Nfind_error_from (N.succ n) x a = Some (N.succ p)) : Nfind_error_from n x a = Some p.
Proof.
  revert e. apply (Nfind_error_from_elim
  (fun (n : N) (x : A) (a : list A) (s : option N) =>
  Nfind_error_from (N.succ n) x a = Some (N.succ p) -> s = Some p)).
  - clear n x a. intros n x e.
    discriminate.
  - clear n x a. intros n x y ex b ed e.
    simp Nfind_error_from in e. rewrite ed in e. simpl in e.
    f_equal. apply N.succ_inj. inversion_clear e. reflexivity.
  - clear n x a. intros n x y ex b es ed e.
    simp Nfind_error_from in e. rewrite ed in e. simpl in e.
    apply es. apply e. Qed.

Lemma Nfind_error_from_succ_iff (n p : N) (x : A) (a : list A) :
  Nfind_error_from n x a = Some p <-> Nfind_error_from (N.succ n) x a = Some (N.succ p).
Proof.
  split.
  - apply Nfind_error_from_succ.
  - apply Nfind_error_from_succ'. Qed.

Lemma Nfind_error_from_succ_zero (n : N) (x : A) (a : list A)
  (e : Nfind_error_from (N.succ n) x a = Some 0) : 0.
Proof.
  revert e. apply (Nfind_error_from_elim
  (fun (n : N) (x : A) (a : list A) (s : option N) =>
  Nfind_error_from (N.succ n) x a = Some 0 -> 0)).
  - clear n x a. intros n x e.
    discriminate.
  - clear n x a. intros n x y ex b ed e.
    simp Nfind_error_from in e. rewrite ed in e. simpl in e.
    injection e. lia.
  - clear n x a. intros n x y ex b f ed e.
    simp Nfind_error_from in e. rewrite ed in e. simpl in e.
    apply f. apply e. Qed.

Lemma Nfind_error_from_lt (n p : N) (x : A) (a : list A)
  (i : p < n) (e : Nfind_error_from n x a = Some p) : 0.
Proof.
  revert p i e. induction n as [| q f] using N.peano_ind; intros p i e.
  - lia.
  - destruct p as [| r _] using N.peano_ind.
    + apply Nfind_error_from_succ_zero in e. contradiction.
    + apply Nfind_error_from_succ' in e. apply f in e.
      * contradiction.
      * lia. Qed.

Lemma Nfind_error_from_some (n p : N) (x y : A) (a : list A)
  (e : Nfind_error_from n x a = Some (n + p)) :
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
        simp Nfind_error_from in e. rewrite ed in e. simpl in e.
        apply Nfind_error_from_lt in e.
        -- contradiction.
        -- lia.
    + destruct (dec (x == z)) as [ex | fx] eqn : ed.
      * exfalso. simp Nfind_error_from in e. rewrite ed in e. simpl in e.
        injection e. lia.
      * simp Nfind_error_from in e. rewrite ed in e. simpl in e.
        pose proof c (N.succ n) q as cq.
        rewrite <- N.add_succ_comm in e. apply cq in e. destruct e as [i [iq ex]].
        split.
        -- right. apply i.
        -- split.
           ++ simp N_length. lia.
           ++ rewrite Nth_succ. apply ex. Qed.

Lemma Nfind_error_from_none (n : N) (x : A) (a : list A)
  (e : Nfind_error_from n x a = None) (s : IsIn x a) : 0.
Proof.
  revert n e s. induction a as [| z b c]; intros n e s.
  - contradiction.
  - simpl in s. destruct s as [t | t].
    + destruct (dec (x == z)) as [ex | fx] eqn : ed.
      * exfalso. simp Nfind_error_from in e. rewrite ed in e. simpl in e.
        discriminate.
      * contradiction.
    + destruct (dec (x == z)) as [ex | fx] eqn : ed.
      * simp Nfind_error_from in e. rewrite ed in e. simpl in e.
        discriminate.
      * simp Nfind_error_from in e. rewrite ed in e. simpl in e.
        revert t. eapply c. apply e. Qed.

Lemma Nfind_error_some (x y : A) (a : list A) (n : N) (s : Nfind_error x a = Some n) :
  IsIn x a /\ n < N_length a /\ Nth n a y == x.
Proof. eapply Nfind_error_from_some. rewrite N.add_0_l. apply s. Qed.

Lemma Nfind_error_none (x : A) (a : list A)
  (s : Nfind_error x a = None) (i : IsIn x a) : 0.
Proof. eapply Nfind_error_from_none. apply s. apply i. Qed.

Lemma Nfind_error_from_some' (n : N) (x y : A) (a : list A) (s : IsIn x a) :
  exists p : N,
  Nfind_error_from n x a = Some (n + p) /\ p < N_length a /\ Nth p a y == x.
Proof.
  revert n s. induction a as [| z b c]; intros n s.
  - contradiction.
  - simpl in s.
    destruct (dec (x == z)) as [ex | fx] eqn : ed.
    + exists 0. repeat split.
      * simp Nfind_error_from. rewrite ed. simpl.
        rewrite N.add_0_r. reflexivity.
      * simp N_length. lia.
      * symmetry. apply ex.
    + destruct s as [t | t].
      * contradiction.
      * simp Nfind_error_from. rewrite ed. cbn -[Nth].
        pose proof c n t as c'. destruct c' as [p [c0 [c1 c2]]].
        exists (N.succ p). repeat split.
        -- rewrite N.add_succ_r. apply Nfind_error_from_succ. apply c0.
        -- lia.
        -- rewrite Nth_ref. unfold Ref.Nth. rewrite N2Nat.inj_succ.
           simpl. rewrite Nth_ref in c2. apply c2. Qed.

Lemma Nfind_error_some' (x y : A) (a : list A) (s : IsIn x a) :
  exists n : N,
  Nfind_error x a = Some n /\ n < N_length a /\ Nth n a y == x.
Proof. eapply Nfind_error_from_some'. apply s. Qed.

Lemma Nfind_error_Nth (n : N) (a : list A) (x : A) (s : n < N_length a) :
  exists p : N,
  Nfind_error (Nth n a x) a = Some p /\ p <= n /\ Nth p a x == Nth n a x.
Proof. Admitted.

Lemma Nfind_from_succ (x : A) (a : list A) (n p : N) (s : IsIn x a) :
  Nfind_from (N.succ n) x a p = N.succ (Nfind_from (N.succ n) x a p).
Proof. Admitted.

Lemma Nfind_from_le (x : A) (a : list A) (n p q : N) (s : IsIn x a)
  (t : Nfind_from n x a p = q) : n <= q /\ q < n + N_length a.
Proof. Admitted.

Lemma Nfind_from_nope (x : A) (a : list A) (n p q : N) (s : ~ IsIn x a)
  (t : Nfind_from n x a p = q) : q = p.
Proof. Admitted.

Lemma Nth_Nfind_from (x y : A) (a : list A) (n p : N) (s : IsIn x a) :
  Nth (Nfind_from n x a p - n) a y == x.
Proof.
  revert s. apply Nfind_from_elim.
  - clear x a n p. intros n x p s. contradiction.
  - clear x a n p. intros n x z t b p t' s. rewrite N.sub_diag. symmetry. apply t.
  - clear x a n p. intros n x z t b p f t' s.
    simpl in s. destruct s as [s' | s'].
    + contradiction.
    + assert (u : n < Nfind_from (N.succ n) x b p).
      { pose proof Nfind_from_le x b (N.succ n) p s' (refl _). lia. }
      pose proof N.lt_exists_pred n (Nfind_from (N.succ n) x b p) u as v.
      destruct v as [q [e i]].
      rewrite e. rewrite N.sub_succ_l by lia. rewrite Nth_succ.
      specialize (f s').
      rewrite Nfind_from_succ in f by assumption.
      rewrite N.sub_succ in f.
      rewrite e in f.
      rewrite <- f.
      (** Nonsense! *)
Admitted.

Lemma Nth_Nfind (x y : A) (a : list A) (p : N) (s : IsIn x a) :
  Nth (Nfind x a p) a y == x.
Proof.
  apply Nfind_elim. rewrite <- (N.sub_0_r (Nfind_from _ _ _ _)).
  apply Nth_Nfind_from. apply s. Qed.
 
End Context.

Lemma map_compose (A B C : Type) (f : A -> B) (g : B -> C) (a : list A) :
  map g (map f a) = map (g o f) a.
Proof. apply map_map. Qed.

Section Context.

Context (A B : Type)
  {X : HasEquivRel A} {d : HasEquivDec A}
  {Y : HasEquivRel B} {e : HasEquivDec B}
  `{!IsEquiv X} `{!IsEquiv Y}.

Lemma IsIn_map (f : A -> B) `{!IsProper (X ==> Y) f} (a : list A) (x : A)
  (s : IsIn x a) : IsIn (f x) (map f a).
Proof.
  revert x s. induction a as [| y b t]; intros x s.
  - contradiction.
  - simpl in s. destruct s as [ex | fx].
    + left. rewrite ex. reflexivity.
    + right. apply t. apply fx. Qed.

Lemma map_ext_equiv
  (f g : A -> B) (s : forall x : A, f x == g x) (a : list A) :
  map f a == map g a.
Proof.
  induction a as [| x b t].
  - reflexivity.
  - simpl map. rewrite s. rewrite t. reflexivity. Qed.

Lemma map_ext_in_equiv
  (f g : A -> B) (a : list A)
  (s : forall (x : A) (t : IsIn x a), f x == g x) :
  map f a == map g a.
Proof.
  induction a as [| x b t].
  - reflexivity.
  - simpl map. rewrite s. rewrite t. reflexivity. Admitted.

Lemma map_in_ext_equiv
  (f g : A -> B) (a : list A) (s : map f a == map g a) (x : A) (t : In x a) :
  f x == g x.
Proof.
  induction a as [| y b u].
  - contradiction.
  - simpl map in s. destruct t as [v | v].
    + apply u. Admitted.

End Context.

(** ** Unsorted Enumeration of a Type *)

(** This is a generalization of [Full]. *)

Class IsFull (A : Type) (X : A -> A -> Prop) (a : list A) : Prop :=
  full (x : A) : Exists (X x) a.

(** ** Uniqueness of a Listing *)

(** This is a generalization of [NoDup]. *)

Section Context.

Context (A : Type) (X : A -> A -> Prop).

#[local] Instance has_equiv_rel : HasEquivRel A := X.

Inductive IsNoDup : list A -> Prop :=
  | IsNoDup_nil : IsNoDup []
  | IsNoDup_cons (x : A) (a : list A) (f : ~ IsIn x a)
    (s : IsNoDup a) : IsNoDup (x :: a).

Existing Class IsNoDup.

End Context.

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

(** Then in Bishop-style, which is missing from the diagram... *)

Equations Fin_of_nat (n : nat) (s : {p : nat | (p < n)%nat}) :
  Fin.t n by struct n :=
  Fin_of_nat (n := O) (p; i) := _;
  Fin_of_nat (n := S _) (O; i) := Fin.F1;
  Fin_of_nat (n := S q) (S p; i) := Fin.FS (Fin_of_nat (n := q) (p; _)).
Next Obligation. cbv beta. intros _ p i. lia. Defined.
Next Obligation. cbv beta. intros _ q p i. lia. Defined.

(** ** Size of a Type *)

Class IsBishopSize (A : Type) (X : A -> A -> Prop) (n : N) : Prop :=
  bishop_size_is_equiv_types :> IsEquivTypes (Fin.t (N.to_nat n)) A _=_ X.

(** ** Finiteness in Terms of Counting *)

Class IsBishopFinSize (A : Type) (X : A -> A -> Prop) : Prop :=
  bishop_fin_size : exists n : N, IsBishopSize X n.

#[export] Instance bishop_size_is_bishop_fin_size (A : Type) (X : A -> A -> Prop)
  (n : N) `{!IsBishopSize X n} : IsBishopFinSize X.
Proof. exists n. auto. Qed.

(** ** Lemmas *)

#[export] Instance nat_has_equiv_rel : HasEquivRel nat := eq.

#[export] Instance sig_has_equiv_rel (A : Type) (P : A -> Prop)
  {X : HasEquivRel A} : HasEquivRel {x : A | P x} :=
  fun x y : {x : A | P x} => proj1_sig x == proj1_sig y.

Lemma sig_N_of_nat (n : nat) (a : {p : nat | p < n}%nat) : {p : N | p < N.of_nat n}.
Proof. destruct a as [p i]. exists (N.of_nat p). lia. Defined.

Lemma sig_N_to_nat (n : nat) (a : {p : N | p < N.of_nat n}) : {p : nat | p < n}%nat.
Proof. destruct a as [p i]. exists (N.to_nat p). lia. Defined.

Lemma sig_N_of_nat' (n : N) (a : {p : nat | p < N.to_nat n}%nat) : {p : N | p < n}.
Proof. destruct a as [p i]. exists (N.of_nat p). lia. Defined.

Lemma sig_N_to_nat' (n : N) (a : {p : N | p < n}) : {p : nat | p < N.to_nat n}%nat.
Proof. destruct a as [p i]. exists (N.to_nat p). lia. Defined.

Lemma obvious (n : nat) x : Fin.to_nat (m := n) (Fin_of_nat x) = x.
Proof. Admitted.

Lemma obvious' (n : nat) x : Fin_of_nat (n := n) (Fin.to_nat x) = x.
Proof. Admitted.

Lemma evident n x : sig_N_of_nat' n (sig_N_to_nat' n x) = x.
Proof. Admitted.

Lemma evident' n x : sig_N_to_nat' n (sig_N_of_nat' n x) = x.
Proof. Admitted.

Lemma bishop_or_not (A : Type) (X : A -> A -> Prop) (n : N) :
  IsBishopSize X n <-> IsSize X n.
Proof.
  split.
  - intros [f [g [r s]]]. hnf.
    exists (f o Fin_of_nat o sig_N_to_nat' _).
    exists (sig_N_of_nat' _ o Fin.to_nat o g).
    split.
    + intros [p i]. unfold compose. rewrite retr.
      rewrite obvious. rewrite evident. reflexivity.
    + intros x. unfold compose.
      rewrite evident'. rewrite obvious'. apply sect.
  - intros [f [g [r s]]]. hnf.
    exists (f o sig_N_of_nat' _ o Fin.to_nat).
    exists (Fin_of_nat o sig_N_to_nat' _ o g).
    split.
    + intros x. unfold compose. rewrite retr.
      rewrite evident'. rewrite obvious'. reflexivity.
    + intros x. unfold compose.
      rewrite obvious. rewrite evident. apply sect. Admitted.

Lemma Nindex_In (A : Type)
  (n : N) (x : A) (a : list A) (s : In (n, x) (Nindex a)) :
  n < N.of_nat (length a).
Proof.
  rewrite Nindex_ref in s. unfold Ref.Nindex, Ref.nindex, Ref.nindex_from in s.
  rewrite map_bimap_combine in s.
  apply in_combine_l in s. apply (in_map N.to_nat) in s.
  rewrite map_map in s. rewrite (map_ext _ id) in s.
  - rewrite map_id in s. apply in_seq in s. lia.
  - intros p. rewrite Nat2N.id. reflexivity. Qed.

Lemma Nindex_length (A : Type) (a : list A) : length (Nindex a) = length a.
Proof.
  rewrite Nindex_ref. unfold Ref.Nindex. unfold Ref.nindex, Ref.nindex_from.
  rewrite map_length. rewrite combine_length. rewrite seq_length.
  rewrite Min.min_idempotent. reflexivity. Qed.

Lemma Nindex_nth (A : Type)
  (n : N) (x : A) (a : list A) (s : n < N.of_nat (length a)) :
  nth (N.to_nat n) (Nindex a) (N.of_nat 0, x) = (n, nth (N.to_nat n) a x).
Proof.
  rewrite Nindex_ref. unfold Ref.Nindex. unfold Ref.nindex, Ref.nindex_from.
  rewrite map_bimap_combine. rewrite combine_nth.
  - f_equal.
    + rewrite map_nth. rewrite seq_nth.
      * lia.
      * lia.
    + rewrite map_id. reflexivity.
  - rewrite map_length. rewrite seq_length. rewrite map_id. reflexivity. Qed.

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
    | x :: b eqn : _ => snd (nth (N.to_nat p) (Nindex (x :: b)) (0, x))
  }.
Next Obligation with notations enabled.
  cbv beta...
  intros p t u. rewrite u in t. unfold length, N.of_nat in t. lia. Qed.

Equations decode (x : A) : {p : N | p < N.of_nat (length (enum A))} :=
  decode x with inspect (Nfind_error x (enum A)) := {
    | Some p eqn : _ => (p; _)
    | None eqn : _ => _
  }.
Next Obligation with notations enabled.
  cbv beta...
  intros x p s. apply (Nfind_error_some x x (enum A)) in s.
  destruct s as [i [ip ex]]. rewrite N_length_ref in ip. apply ip. Qed.
Next Obligation with notations enabled.
  cbv beta...
  intros x t. exfalso.
  apply (Nfind_error_none x a).
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

Equations map_with_sig (A B : Type) (P : A -> Prop)
  (f : forall x : A, P x -> B) (a : list A) (s : Forall P a) :
  list B by struct a :=
  map_with_sig f (a := []) s := [];
  map_with_sig f (a := x :: b) s :=
  f x (Forall_inv s) :: map_with_sig f (a := b) (Forall_inv_tail s).

Arguments map_with_sig {_ _ _} _ _ _.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (d : forall x y : A, {X x y} + {~ X x y}) (a : list A) `{!IsEquiv X}.

#[local] Instance has_equiv_rel' : HasEquivRel A := X.
#[local] Instance has_equiv_dec : HasEquivDec A := d.
#[local] Instance has_enum : HasEnum A := a.

Ltac notations f := progress (
  f X (equiv_rel (A := A));
  f d (equiv_dec (A := A));
  f a (enum A)).

(** TODO Prove the equivalence of these definitions. *)

#[export] Instance listing_is_size_length
  `{!IsListing X a} : IsSize X (N_length a).
Proof with notations enabled.
  rewrite N_length_ref. unfold Ref.N_length.
  exists encode, decode... split.
  - intros [p t]. apply encode_elim.
    + clear p t. intros p t u _. exfalso.
      rewrite u in t. unfold length, N.of_nat in t. lia.
    + clear p t. intros p t x b u _. rewrite Nindex_nth.
      * unfold snd.
        remember (nth (N.to_nat p) (x :: b) x) as k eqn : ek.
        revert t u ek.
        apply decode_elim.
        -- clear k. intros y q vf _ t vt ve.
           pose proof vf as vf'.
           apply (Nfind_error_some y x (enum A)) in vf'.
           subst y. destruct vf' as [h0 [h1 v]].
           rewrite Nth_ref in v. simp Nth in v. rewrite <- vt in v.
           assert (m' : q = p).
           { apply nth_inversion in v. lia. rewrite N_length_ref in h1.
             unfold Ref.N_length in h1. lia. lia. }
           match goal with
           | |- (?p; ?a) = (?q; ?b) =>
             apply (eq_exist_curried
             (P := fun p => p < N.of_nat (length (enum A)))
             (u1 := p) (v1 := q) (u2 := a) (v2 := b) m')
           end. apply irrel.
        -- clear k. intros y vf _ t vt ve. exfalso.
           apply Nfind_error_none in vf.
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
        rewrite Nindex_nth.
        -- unfold snd. clear et.
           rewrite <- u.
           apply (Nfind_error_some x z) in s.
           destruct s as [ix [i e]].
           rewrite Nth_ref in e. apply e.
        -- rewrite <- u. lia.
    + clear x. intros x s _. exfalso.
      apply Nfind_error_none in s. contradiction.
      pose proof full x as fz. apply Exists_IsIn in fz.
      destruct fz as [z [i e]].
      pose proof Proper_IsIn z x (enum A) as w. apply w.
      symmetry. apply e. apply i. Qed.

#[export] Instance listing_is_size_length'
  `{!IsListing X a} : IsBishopSize X (N_length a).
Proof. apply bishop_or_not. apply listing_is_size_length. Qed.

#[local] Instance size_length_is_listing'
  `{!IsBishopSize X (N_length a)} : IsListing X a.
Proof.
  split...
  - intros x.
    pose proof bishop_size_is_equiv_types as t.
    pose proof equiv_types _ _ _ _ (IsEquivTypes := t) as u.
    destruct u as [f [g [r s]]]. hnf in r, s. clear IsBishopSize0 t.

    apply IsIn_Exists.
    exists x. split; try reflexivity.

Admitted.

Equations N_seq_sig' (n p : N) : list {q : N | q < n + p} :=
  N_seq_sig' n p with inspect (N_seq n p) := {
    | a eqn : _ => _
  }.
Next Obligation.
  intros n p b s.
  revert n b s; induction p as [| q t] using N.peano_rect; intros n b s.
  - apply nil.
  - rewrite N_seq_ref in s. unfold Ref.N_seq in s.
    rewrite N2Nat.inj_succ in s. rewrite <- cons_seq in s.
    rewrite map_cons in s. destruct b as [| x b].
    + discriminate.
    + inversion s as [[sx sb]]. clear s. apply cons.
      * exists x. lia.
      * rewrite N.add_succ_r. rewrite <- N.add_succ_l.
        pose proof t (N.succ n) b as t'. apply t'.
        rewrite N_seq_ref. unfold Ref.N_seq.
        rewrite N2Nat.inj_succ. apply sb. Defined.

Equations N_seq_sig (n p : N) : list {q : N | q < n + p} :=
  N_seq_sig n p := map_with_sig (P := fun q : N => q < n + p) _ (N_seq n p) _.
Next Obligation. cbv beta. intros n p q i. exists q. lia. Defined.
Next Obligation. cbv beta. intros n p.
  revert n; induction p as [| q s] using N.peano_rect; intros n.
  simp N_seq. apply Forall_nil.
  rewrite N_seq_ref. unfold Ref.N_seq. rewrite N2Nat.inj_succ. rewrite <- cons_seq.
  rewrite map_cons.
  rewrite <- N2Nat.inj_succ.
  change (map N.of_nat (seq (N.to_nat (N.succ n)) (N.to_nat q))) with (Ref.N_seq (N.succ n) q).
  rewrite <- N_seq_ref.
  apply Forall_cons. lia.
  replace (n + N.succ q) with (N.succ n + q) by lia.
  apply s. Defined.

From Coq Require Import Logic.FinFun Sorting.Permutation.

#[local] Instance size_length_is_listing
  `{!IsSize X (N_length a)} : IsListing X a.
Proof with notations enabled.
  split...
  - intros x.
    pose proof size_is_equiv_types as t.
    pose proof equiv_types _ _ _ _ (IsEquivTypes := t) as u.
    destruct u as [f [g [r s]]]. hnf in r, s. clear IsSize0 t.

    remember (N_length (enum A)) as n eqn : t.
    assert (t' : n <= N_length (enum A)) by lia.
    clear t.
    generalize dependent g.
    generalize dependent f.
    induction n as [| q i] using N.peano_ind; intros.
    destruct (g x) as [oh fuck]. lia.
    eset (f' (a : {p : N | p < q}) := match a with
    | (p; i) => f (p; _)
    end : A).
    eset (g' (y : A) := match g y with
    | (p; i) => (p; _)
    end : {p : N | p < q}).
    apply (i ltac:(lia) f' g'). Unshelve. all: cbv beta.
    intros [p l]. unfold f', g'. simpl. rewrite r. f_equal. apply irrel.
    intros y. unfold f', g'. destruct (g y) as [p j] eqn : egg.
    match goal with
    | |- f (p; ?hole) == y => rewrite (irrel hole j)
    end. rewrite <- egg. rewrite s. reflexivity.
    lia.
    clearbody f'.

    (* set (f' := sig_curry f). cbv beta in f'.
    set (g' := proj1_sig o g).
    assert (g'wd : forall x : A, g' x < N.of_nat (length (enum A))).
    { intros y. unfold g'. unfold compose. destruct (g y) as [gy i].
      simpl. apply i. }
    assert (r' : forall (p : N) (i : p < N.of_nat (length (enum A))),
    g' (f' p i) = p).
    { intros p i. unfold f', g'. unfold compose.
      rewrite r. reflexivity. } *)

    (** To go from [IsIn x (enum A)] to [In (g x) (map g (enum A))]. *)
    (*
    change x with (id x).
    epose proof Proper_IsIn ((f o g) x) (id x) _ (s _) as P. apply P. clear P.
    rewrite <- (map_id (enum A)).
    change (fun x : A => x) with (@id A).
    rewrite (map_ext_equiv id (f o g)).
    2:{ intros ?. symmetry. apply s. }
    rewrite <- (map_compose g f).
    unfold compose.
    eapply IsIn_map.
    enough (talk : In (g x) (map g (enum A))) by apply talk.
    *)

    admit.
  - pose proof size_is_equiv_types as t.
    pose proof equiv_types _ _ _ _ (IsEquivTypes := t) as u.
    destruct u as [f [g [r s]]].
    hnf in r, s.

    admit.
Admitted.

End Context.

Lemma N_seq_sig_proj1_sig (n p : N) : map proj1_sig (N_seq_sig n p) = N_seq n p.
Proof. Admitted.

Section Context.

Context (A : Type) (P : A -> Prop).

Equations list_proj1_sig (a : list {x : A | P x}) : list A by struct a :=
  list_proj1_sig [] := [];
  list_proj1_sig ((x; _) :: b) := x :: list_proj1_sig b.

Lemma list_proj2_sig (a : list {x : A | P x}) : Forall P (list_proj1_sig a).
Proof.
  induction a as [| [x a] b s].
  - apply Forall_nil.
  - simp list_proj1_sig. apply Forall_cons.
    + apply a.
    + apply s. Qed.

End Context.

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (d : forall x y : A, {X x y} + {~ X x y}) `{!IsEquiv X}.

#[local] Instance has_equiv_rel'' : HasEquivRel A := X.
#[local] Instance has_equiv_dec' : HasEquivDec A := d.

#[export] Instance fin_listing_is_fin_size
  `{!IsFinListing X} : IsFinSize X.
Proof.
  destruct fin_listing as [a ?]. exists (N_length a).
  apply listing_is_size_length; eauto || typeclasses eauto. Qed.

#[local] Instance fin_size_is_fin_listing
  `{!IsFinSize X} : IsFinListing X.
Proof.
  destruct fin_size as [n s]. pose proof s as t.
  destruct t as [f [g ?]]. exists (map f (N_seq_sig 0 n)).
  apply size_length_is_listing; try eauto || typeclasses eauto.
  rewrite N_length_ref. unfold Ref.N_length.
  rewrite map_length. rewrite <- (map_length proj1_sig (N_seq_sig 0 n)).
  rewrite N_seq_sig_proj1_sig.
  rewrite N_seq_ref. unfold Ref.N_seq.
  rewrite map_length. rewrite seq_length. rewrite N2Nat.id.
  typeclasses eauto. Qed.

End Context.
