(** Positive maps based on Robbert Krebbers's implementation
    based on Xavier Leroy's implementation based on ancient history,
    except there is a total order and a pruning function involved. *)

From Coq Require Import
  PArith.PArith.
From Maniunfold.Has Require Export
  OneSorted.EqualityDecision OneSorted.Unsquashing.

From Coq Require Import Lia List Recdef.
Import ListNotations Pos.

Local Open Scope positive_scope.

Inductive pos_tree (A : Type) : Type :=
  | pos_leaf : pos_tree A
  | pos_branch (x : option A) (l : pos_tree A) (r : pos_tree A) : pos_tree A.

Arguments pos_leaf {_}.

Global Instance bool_has_eq_dec : HasEqDec bool.
Proof. cbv [HasEqDec]. decide equality. Defined.

Global Instance positive_has_eq_dec : HasEqDec positive.
Proof. cbv [HasEqDec] in *. decide equality. Defined.

Global Instance positive_has_le_dec (n p : positive) : HasDec (n <= p).
Proof.
  cbv [HasDec] in *. destruct (n <=? p) eqn : e.
  - left. apply leb_le; auto.
  - right. apply leb_nle; auto. Defined.

Global Instance positive_has_lt_dec (n p : positive) : HasDec (n < p).
Proof.
  cbv [HasDec] in *. destruct (n <? p) eqn : e.
  - left. apply ltb_lt; auto.
  - right. apply ltb_nlt; auto. Defined.

Global Instance option_has_eq_dec (A : Type) `(HasEqDec A) :
  HasEqDec (option A).
Proof. cbv [HasEqDec] in *. decide equality. Defined.

Global Instance pos_tree_has_eq_dec (A : Type) `(HasEqDec A) :
  HasEqDec (pos_tree A).
Proof. cbv [HasEqDec]. decide equality. apply EqualityDecision.eq_dec. Defined.

Fixpoint pos_tree_wf' (A : Type) (t : pos_tree A) : bool :=
  match t with
  | pos_leaf => true
  | pos_branch None pos_leaf pos_leaf => false
  | pos_branch x l r => pos_tree_wf' l && pos_tree_wf' r
  end.

Arguments pos_tree_wf' _ !_.

Definition pos_tree_wf (A : Type) (t : pos_tree A) : Prop :=
  is_true (pos_tree_wf' t).

Arguments pos_tree_wf _ !_.

(** Forward reasoning for well-formedness. *)

Definition pos_branch' (A : Type) (x : option A) (l r : pos_tree A) :=
  match x, l, r with
  | None, pos_leaf, pos_leaf => pos_leaf
  | _, _, _ => pos_branch x l r
  end.

Lemma pos_tree_wf_leaf (A : Type) : pos_tree_wf (@pos_leaf A).
Proof. Admitted.

Lemma pos_tree_wf_branch (A : Type) (x : option A) (l r : pos_tree A)
  (wl : pos_tree_wf l) (wr : pos_tree_wf r) : pos_tree_wf (pos_branch' x l r).
Proof. Admitted.

Local Hint Resolve pos_tree_wf_leaf pos_tree_wf_branch : core.

(** Backward reasoning for well-formedness. *)

Lemma pos_tree_wf_l (A : Type) (x : option A)
  (l r : pos_tree A) (w : pos_tree_wf (pos_branch x l r)) : pos_tree_wf l.
Proof.
  destruct x, l, r; constructor ||
  cbv [pos_tree_wf pos_tree_wf'] in w; apply andb_prop in w; destruct w;
  tauto. Qed.

Lemma pos_tree_wf_r (A : Type) (x : option A)
  (l r : pos_tree A) (w : pos_tree_wf (pos_branch x l r)) : pos_tree_wf r.
Proof.
  destruct x, l, r; constructor ||
  cbv [pos_tree_wf pos_tree_wf'] in w; apply andb_prop in w; destruct w;
  tauto. Qed.

Local Hint Resolve pos_tree_wf_l pos_tree_wf_r : core.

Definition pos_tree_empty (A : Type) : pos_tree A := pos_leaf.

Fixpoint pos_tree_lookup (A : Type)
  (n : positive) (t : pos_tree A) : option A :=
  match t with
  | pos_leaf => None
  | pos_branch x l r =>
    match n with
    | xH => x
    | xO p => @pos_tree_lookup A p l
    | xI p => @pos_tree_lookup A p r
    end
  end.

Arguments pos_tree_lookup _ !_ !_.

Fixpoint pos_tree_singleton (A : Type) (n : positive) (x : A) : pos_tree A :=
  match n with
  | xH => pos_branch (Some x) pos_leaf pos_leaf
  | xO p => pos_branch None (@pos_tree_singleton A p x) pos_leaf
  | xI p => pos_branch None pos_leaf (@pos_tree_singleton A p x)
  end.

Arguments pos_tree_singleton _ !_ _.

Lemma pos_tree_wf_singleton (A : Type) (n : positive) (x : A) :
  pos_tree_wf (pos_tree_singleton n x).
Proof.
  induction n.
  - cbn; destruct n; auto.
  - cbn; destruct n; rewrite Bool.andb_true_r; apply IHn.
  - reflexivity. Qed.

Fixpoint pos_tree_partial_alter' (A : Type) (f : option A -> option A)
  (n : positive) (t : pos_tree A) {struct t} : pos_tree A :=
  match t with
  | pos_leaf =>
    match f None with
    | Some x => pos_tree_singleton n x
    | None => pos_leaf
    end
  | pos_branch x l r =>
     match n with
     | xH => pos_branch' (f x) l r
     | xO p => pos_branch' x (@pos_tree_partial_alter' A f p l) r
     | xI p => pos_branch' x l (@pos_tree_partial_alter' A f p r)
     end
  end.

Arguments pos_tree_partial_alter' _ _ !_ !_.

Definition pos_tree_partial_alter (A : Type) (f : option A -> option A)
  (t : pos_tree A) : pos_tree A :=
  pos_tree_partial_alter' f xH t.

Arguments pos_tree_partial_alter _ _ !_.

Fixpoint pos_tree_map (A B : Type) (f : A -> B) (t : pos_tree A) : pos_tree B :=
  match t with
  | pos_leaf => pos_leaf
  | pos_branch x l r => pos_branch (option_map f x)
    (@pos_tree_map A B f l) (@pos_tree_map A B f r)
  end.

Arguments pos_tree_map _ _ _ !_.

(** Replicating sequence A059893. *)

Fixpoint pos_reverse' (n p : positive) : positive :=
  match p with
  | xI q => pos_reverse' (xI n) q
  | xO q => pos_reverse' (xO n) q
  | xH => n
  end.

Definition pos_reverse (n : positive) : positive := pos_reverse' xH n.

(* Compute map pos_reverse [xH;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16]%positive. *)

Fixpoint pos_tree_to_list' (A : Type) (n : positive)
  (a : list (positive * A)) (t : pos_tree A) : list (positive * A) :=
  match t with
  | pos_leaf => a
  | pos_branch x l r =>
    let k := @pos_tree_to_list' A (xO n) (@pos_tree_to_list' A (xI n) a r) l in
    match x with
    | Some y => cons (n, y) k
    | None => k
    end
  end.

Arguments pos_tree_to_list' _ _ _ !_.

Definition pos_tree_to_list (A : Type) (t : pos_tree A) :
  list (positive * A) :=
  pos_tree_to_list' xH nil t.

Arguments pos_tree_to_list _ !_.

Compute pos_tree_to_list (pos_branch (Some xH) pos_leaf pos_leaf).
Compute pos_tree_to_list
  (pos_branch None
    (pos_branch (Some 2)
      (pos_branch (Some 4) pos_leaf pos_leaf)
      (pos_branch (Some 5) pos_leaf pos_leaf))
    (pos_branch (Some 3)
      pos_leaf
      (pos_branch (Some 7) pos_leaf pos_leaf))).

(** Merge sort passionately! *)

Function merge' (l : list positive * list positive)
  {measure (fun l : list positive * list positive =>
    length (app (fst l) (snd l))) l} : list positive :=
  let (l0, l1) := l in
  match l0, l1 with
  | nil, _ => l1
  | _, nil => l0
  | cons n0 k0, cons n1 k1 => if n0 <=? n1 then
    cons n0 (@merge' (k0, l1)) else
    cons n1 (@merge' (l0, k1))
  end.
Proof.
  - intros. cbn in *. lia.
  - intros. repeat rewrite app_length. cbn in *. lia. Defined.

Arguments merge' _ / : simpl nomatch.

Definition merge (l0 l1 : list positive) : list positive := merge' (l0, l1).

Arguments merge !_ !_.

Function merge_by' (A : Type) (f : A -> positive) (l : list A * list A)
  {measure (fun l : list A * list A =>
    let (l0, l1) := l in
    length (app l0 l1)) l} : list A :=
  let (l0, l1) := l in
  match l0, l1 with
  | nil, _ => l1
  | _, nil => l0
  | cons n0 k0, cons n1 k1 => if f n0 <=? f n1 then
    cons n0 (@merge_by' A f (k0, l1)) else
    cons n1 (@merge_by' A f (l0, k1))
  end.
Proof.
  - intros. cbn in *. lia.
  - intros. repeat rewrite app_length. cbn in *. lia. Defined.

Arguments merge_by' _ _ _ / : simpl nomatch.

Definition merge_by (A : Type) (f : A -> positive) (l0 l1 : list A) :
  list A := merge_by' f (l0, l1).

Arguments merge_by _ _ !_ !_.

Fixpoint pos_tree_to_sorted_list' (A : Type) (n : positive)
  (t : pos_tree A) : list (positive * A) :=
  match t with
  | pos_leaf => nil
  | pos_branch x l r =>
    let k := merge_by fst
    (@pos_tree_to_sorted_list' A (xO n) l)
    (@pos_tree_to_sorted_list' A (xI n) r) in
    match x with
    | Some y => cons (n, y) k
    | None => k
    end
  end.

Arguments pos_tree_to_sorted_list' _ _ !_.

Definition pos_tree_to_sorted_list (A : Type) (t : pos_tree A) :
  list (positive * A) :=
  pos_tree_to_sorted_list' xH t.

Arguments pos_tree_to_sorted_list _ !_.

Compute pos_tree_to_sorted_list (pos_branch (Some xH) pos_leaf pos_leaf).
Compute pos_tree_to_sorted_list
  (pos_branch None
    (pos_branch (Some 2)
      (pos_branch (Some 4) pos_leaf pos_leaf)
      (pos_branch (Some 5) pos_leaf pos_leaf))
    (pos_branch (Some 3)
      pos_leaf
      (pos_branch (Some 7) pos_leaf pos_leaf))).

(** Now we struggle. *)

Definition prod_bimap (A B C D : Type)
  (f : A -> B) (g : C -> D) (x : A * C) : B * D :=
  (f (fst x), g (snd x)).

Definition prod_map (A B : Type) (f : A -> B) (x : A * A) : B * B :=
  prod_bimap f f x.

(**
This is the Haskell way.

<<
data PosTree a = PosLeaf | PosBranch (Maybe a) (PosTree a) (PosTree a) deriving (Eq, Ord, Show)

posBranch' x l r = case (x, l, r) of (Nothing, PosLeaf, PosLeaf) -> PosLeaf; _ -> PosBranch x l r
-- This one is suspect.
posTreeOfSortedList n l = case l of [] -> PosLeaf; (p, x) : k -> case compare p n of LT -> posTreeOfSortedList n k; EQ -> PosBranch (Just x) (posTreeOfSortedList (2 * n) k) (posTreeOfSortedList (1 + 2 * n) k); GT -> posBranch' Nothing (posTreeOfSortedList (2 * n) l) (posTreeOfSortedList (1 + 2 * n) l)
posTreeToList n a t = case t of PosLeaf -> a; PosBranch x l r -> let k = posTreeToList (2 * n) (posTreeToList (1 + 2 * n) a r) l in case x of Nothing -> k; Just y -> (n, y) : k
mergeBy f l0 l1 = case (l0, l1) of ([], _) -> l1; (_, []) -> l0; (n0 : k0, n1 : k1) -> if f n0 <= f n1 then n0 : mergeBy f k0 l1 else n1 : mergeBy f l0 k1
posTreeToSortedList n t = case t of PosLeaf -> []; PosBranch x l r -> let k = mergeBy fst (posTreeToSortedList (2 * n) l) (posTreeToSortedList (1 + 2 * n) r) in case x of Nothing -> k; Just y -> (n, y) : k

> posTreeOfSortedList 1 [(2, 2), (3, 3), (4, 4), (5, 5), (7, 7)]
> posTreeToSortedList 1 (posTreeOfSortedList 1 [(2, 2), (3, 3), (4, 4), (5, 5), (7, 7)])
>>
*)

Local Notation "'LT'" := (inleft (left _))
  (at level 0, no associativity, only parsing).
Local Notation "'EQ'" := (inleft (right _))
  (at level 0, no associativity, only parsing).
Local Notation "'GT'" := (inright _)
  (at level 0, no associativity, only parsing).

Definition pos_trichotomy_inf (p q : positive) : {p < q} + {p = q} + {q < p}.
Proof.
  destruct (dec (p < q)), (dec (p = q)), (dec (q < p)); auto || lia. Defined.

Compute let (p, n) := (42, 13) in
    match pos_trichotomy_inf p n with
    | LT => 2
    | EQ => 3
    | GT => 4
    end.
(** This is dumb. *)

Definition pos_max (l : list positive) : positive := fold_right max xH l.

Function pos_tree_of_sorted_list' (A : Type)
  (ln : list (positive * A) * positive)
  {measure (fun ln : list (positive * A) * positive =>
    let (l, n) := ln in
    length l + to_nat (sub (xI (pos_max (map fst l))) n))%nat ln} :
  pos_tree A :=
  let (l, n) := ln in
  match l with
  | nil => pos_leaf
  | cons (p, x) k =>
    match pos_trichotomy_inf p n with
    | LT => @pos_tree_of_sorted_list' A (k, n)
    | EQ => pos_branch (Some x)
      (@pos_tree_of_sorted_list' A (k, xO n))
      (@pos_tree_of_sorted_list' A (k, xI n))
    | GT => pos_branch' None
      (@pos_tree_of_sorted_list' A (l, xO n))
      (@pos_tree_of_sorted_list' A (l, xI n))
    end
  end.
Proof.
  (** Structurally recursive cases. *)
  - intros. cbn in *. cbv [pos_max]. lia.
  - intros. cbn in *. cbv [pos_max]. lia.
  - intros. cbn in *. cbv [pos_max]. lia.
  (** The tricky bits. *)
  - intros. cbn in *.
    (** Natural number wrangle. *)
    apply Lt.lt_n_S. apply Plus.plus_lt_compat_l.
    apply Pos2Nat.inj_lt.
    (** Positive number stuff. *)
    lia.
  (** Again. *)
  - intros. cbn in *.
    apply Lt.lt_n_S. apply Plus.plus_lt_compat_l.
    apply Pos2Nat.inj_lt.
    lia. Defined.

Definition pos_tree_of_sorted_list (A : Type) (l : list (positive * A)) :
  pos_tree A :=
  pos_tree_of_sorted_list' (l, xH).

Compute pos_tree_of_sorted_list ((xH, xH) :: nil)%list.
Compute pos_tree_of_sorted_list ((2, 2) :: nil)%list.
Compute pos_tree_of_sorted_list ((2, 2) :: (3, 3) :: (4, 4) :: (5, 5) :: (7, 7) :: nil)%list.
Compute pos_tree_to_sorted_list (pos_tree_of_sorted_list ((2, 2) :: (3, 3) :: (4, 4) :: (5, 5) :: (7, 7) :: nil)%list).

Fail Definition pos_tree_of_list (A : Type) (l : list (positive * A)) :
  pos_tree A := pos_tree_of_sorted_list (sort l).

Fixpoint pos_tree_omap (A B : Type) (f : A -> option B)
  (t : pos_tree A) : pos_tree B :=
  match t with
  | pos_leaf => pos_leaf
  | pos_branch x l r =>
    pos_branch' match x with
    | Some y => f y
    | None => None
    end (@pos_tree_omap A B f l) (@pos_tree_omap A B f r)
  end.

Fixpoint pos_tree_merge (A B C : Type) (f : option A -> option B -> option C)
  (t0 : pos_tree A) (t1 : pos_tree B) : pos_tree C :=
  match t0, t1 with
  | pos_leaf, t1 => pos_tree_omap (f None o Some) t1
  | t0, pos_leaf => pos_tree_omap (flip f None o Some) t0
  | pos_branch o0 l0 r0, pos_branch o1 l1 r1 =>
    pos_branch' (f o0 o1)
    (@pos_tree_merge A B C f l0 l1)
    (@pos_tree_merge A B C f r0 r1)
  end.

Polymorphic Hint Resolve squash : core.

Definition pos_map (A : Type) : Type :=
  {t : pos_tree A ! Squash (pos_tree_wf t)}.

Global Instance Ssig_has_eq_dec (A : Type) (P : A -> SProp) `(HasEqDec A) :
  HasEqDec (Ssig P).
Proof. cbv [HasEqDec] in *. intros [] []. pose proof H Spr1 Spr0. destruct H0.
  left. apply Spr1_inj. auto.
  right. intros ?. inversion H0. contradiction. Defined.

Global Instance pos_map_has_eq_dec (A : Type) `(HasEqDec A) :
  HasEqDec (pos_map A).
Proof. typeclasses eauto. Defined.

Program Definition pos_map_empty (A : Type) : pos_map A :=
  Sexists (Squash o pos_tree_wf) pos_leaf _.
Next Obligation. eauto. (* intros A. apply squash. reflexivity. *) Qed.

Definition pos_map_lookup (A : Type)
  (i : positive) (m : pos_map A) : option A :=
  pos_tree_lookup i (Spr1 m).

Program Definition pos_map_partial_alter (A : Type)
  (f : option A -> option A) (m : pos_map A) : pos_map A :=
  Sexists (Squash o pos_tree_wf) (pos_tree_partial_alter f (Spr1 m)) _.
Next Obligation.
  intros A f [t w]. apply squash. cbn. apply unsquash in w.
  induction t.
    cbv [pos_tree_partial_alter pos_tree_partial_alter']. destruct (f None).
    apply pos_tree_wf_singleton.
    reflexivity.
    cbn -[pos_tree_wf] in *. all: eauto.
   (* apply pos_tree_wf_branch. eapply pos_tree_wf_l. apply w.
      apply IHt2. eapply pos_tree_wf_r. apply w.
      apply pos_tree_wf_branch. apply IHt1. eapply pos_tree_wf_l. apply w.
      eapply pos_tree_wf_r. apply w.
      apply pos_tree_wf_branch.
      eapply pos_tree_wf_l. apply w.
      eapply pos_tree_wf_r. apply w. *) Qed.

Program Definition pos_map_map (A B : Type)
  (f : A -> B) (m : pos_map A) : pos_map B :=
  Sexists (Squash o pos_tree_wf) (pos_tree_map f (Spr1 m)) _.
Next Obligation. intros A B f [t w]. apply squash. cbn. apply unsquash in w.
  induction t.
    cbv [pos_tree_map]. assumption.
    cbn -[pos_tree_wf] in *. Admitted.

Arguments pos_map_map _ _ _ !_.

Definition pos_map_to_list (A : Type) (m : pos_map A) : list (positive * A) :=
  pos_tree_to_list (Spr1 m).

Definition pos_map_to_sorted_list (A : Type)
  (m : pos_map A) : list (positive * A) :=
  pos_tree_to_sorted_list (Spr1 m).

Program Definition pos_map_omap (A B : Type) (f : A -> option B)
  (m : pos_map A) : pos_map B :=
  Sexists (Squash o pos_tree_wf) (pos_tree_omap f (Spr1 m)) _.
Next Obligation. intros A B f [t w]. apply squash. cbn. apply unsquash in w.
  Admitted.

Program Definition pos_map_merge (A B C : Type)
  (f : option A -> option B -> option C)
  (m0 : pos_map A) (m1 : pos_map B) : pos_map C :=
  Sexists (Squash o pos_tree_wf) (pos_tree_merge f (Spr1 m0) (Spr1 m1)) _.
Next Obligation. intros A B C f [t0 w0] [t1 w1]. apply squash. cbn.
  apply unsquash in w0. apply unsquash in w1. Admitted.

Inductive nat_map (A : Type) : Type :=
  | nat_stump : option A -> pos_map A -> nat_map A.

Global Instance nat_map_has_eq_dec (A : Type) `(HasEqDec A) :
  HasEqDec (nat_map A).
Proof. cbv [HasEqDec]. decide equality.
  all: apply EqualityDecision.eq_dec. Defined.

Definition nat_map_forall (A : Type) (P : A -> Prop) (m : nat_map A) : Prop :=
  forall (i : positive) (x : A), (* nat_map_lookup i m = Some x -> *) P x.

Definition nat_map_iforall (A : Type) (P : positive -> A -> Prop)
  (m : nat_map A) : Prop :=
  forall (i : positive) (x : A), (* nat_map_lookup i m = Some x -> *) P i x.

Definition cut_map_wf (A : Type) (P : A -> Prop) (m : nat_map A) : Prop :=
  nat_map_forall (not o P) m.

(* Arguments cut_map_wf _ _ !_. *)

Definition cut_map (A : Type) (P : A -> Prop) : Type :=
  {m : nat_map A ! Squash (cut_map_wf P m)}.

Lemma Unnamed_goal (A : Type) (P : A -> Prop) (x y : cut_map P) :
  x = y <-> Spr1 x = Spr1 y.
Proof. destruct x, y; cbn. split. intros. inversion H. auto.
  intros w. apply Spr1_inj. cbn. auto. Qed.

(** We can now represent polynomials with [cut_map (eq 0)]. *)

Definition dec_map_wf (A : Type) (p : A -> bool) (m : nat_map A) : Prop :=
  nat_map_forall (is_true o p) m.

(* Arguments dec_map_wf _ _ !_. *)

Definition dec_map (A : Type) (p : A -> bool) : Type :=
  {m : nat_map A ! Squash (dec_map_wf p m)}.

Definition is_left (A B : Prop) (s : sumbool A B) : bool :=
  match s with
  | left _ => true
  | right _ => false
  end.

Lemma Unnamed_goal' (A : Type) (p : A -> bool) (x y : dec_map p) :
  x = y <-> Spr1 x = Spr1 y.
Proof. destruct x, y; cbn. split. intros. inversion H. auto.
  intros w. apply Spr1_inj. cbn. auto. Qed.

(** We can now represent polynomials over discrete rings
    with [dec_map (eqb 0)] or [dec_map (is_left o dec o eq 0)]. *)
