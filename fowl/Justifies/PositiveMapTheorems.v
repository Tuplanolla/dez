(** Positive maps based on Robbert Krebbers's implementation
    based on Xavier Leroy's implementation based on ancient history,
    except there is a total order and a pruning function involved.
    Parts of Hugo Herbelin's merge sort also make an appearance.
    Full credits can be found in the transitive dependencies of this file. *)

From Coq Require Import
  Classes.DecidableClass PArith.PArith Program.Wf.
From DEZ.Has Require Export
  Unsquashings.
From DEZ.Justifies Require Import
  LogicalTheorems OptionTheorems PositiveTheorems PositivePairingFunctions.

From Coq Require Import Lia List Recdef.
Import ListNotations Pos.

(** TODO This breaks [lia] for some reason. *)

#[local] Unset Keyed Unification.

(** TODO Why does this break too? *)

Unset Universe Polymorphism.

Global Instance option_has_equiv_dec (A : Type) `(EqDec A) : EqDec (option A).
Proof. cbv [EqDec] in *. decide equality. Defined.

Fixpoint list_omap (A B : Type) (f : A -> option B)
  (l : list A) {struct l} : list B :=
  match l with
  | [] => []
  | x :: l' =>
    match f x with
    | Some y => y :: list_omap f l'
    | None => list_omap f l'
    end
  end.

Arguments list_omap _ _ _ !_ : simpl nomatch.

Definition pair_diag (A : Type) (a : A) : A * A := (a, a).

Arguments pair_diag _ _ /.

Inductive pos_tree (A : Type) : Type :=
  | pos_leaf : pos_tree A
  | pos_branch (x : option A) (l : pos_tree A) (r : pos_tree A) : pos_tree A.

Arguments pos_leaf {_}.

Global Instance pos_tree_has_equiv_dec (A : Type) `(EqDec A) : EqDec (pos_tree A).
Proof. cbv [EqDec]. decide equality. decide equality. Defined.

Fixpoint pos_tree_wf' (A : Type) (t : pos_tree A) {struct t} : bool :=
  match t with
  | pos_leaf => true
  | pos_branch None pos_leaf pos_leaf => false
  | pos_branch _ l r => pos_tree_wf' l && pos_tree_wf' r
  end.

Arguments pos_tree_wf' _ !_.

Definition pos_tree_wf (A : Type) (t : pos_tree A) : Prop :=
  is_true (pos_tree_wf' t).

Arguments pos_tree_wf _ _ /.

(** Forward reasoning for well-formedness. *)

Definition pos_branch' (A : Type) (x : option A) (l r : pos_tree A) :=
  match x, l, r with
  | None, pos_leaf, pos_leaf => pos_leaf
  | _, _, _ => pos_branch x l r
  end.

Arguments pos_branch' _ !_ !_ !_.

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

#[local] Hint Resolve pos_tree_wf_l pos_tree_wf_r : core.

Lemma pos_tree_wf_leaf (A : Type) : pos_tree_wf (@pos_leaf A).
Proof. cbn; auto. Qed.

Lemma pos_tree_wf_branch (A : Type) (a : A) (l r : pos_tree A)
  (wl : pos_tree_wf l) (wr : pos_tree_wf r) :
  pos_tree_wf (pos_branch (Some a) l r).
Proof. cbn; auto with bool. Qed.

Lemma pos_tree_wf_branch' (A : Type) (x : option A) (l r : pos_tree A)
  (wl : pos_tree_wf l) (wr : pos_tree_wf r) : pos_tree_wf (pos_branch' x l r).
Proof. destruct x, l, r; cbn; auto with bool. Qed.

#[local] Hint Resolve pos_tree_wf_leaf
  pos_tree_wf_branch pos_tree_wf_branch' : core.

Definition pos_tree_empty (A : Type) : pos_tree A := pos_leaf.

Arguments pos_tree_empty _ /.

Fixpoint pos_tree_lookup (A : Type)
  (n : positive) (t : pos_tree A) {struct t} : option A :=
  match t with
  | pos_leaf => None
  | pos_branch x l r =>
    match n with
    | xH => x
    | xO p => pos_tree_lookup p l
    | xI p => pos_tree_lookup p r
    end
  end.

Arguments pos_tree_lookup _ !_ !_.

Fixpoint pos_tree_singleton (A : Type)
  (n : positive) (x : A) {struct n} : pos_tree A :=
  match n with
  | xH => pos_branch (Some x) pos_leaf pos_leaf
  | xO p => pos_branch None (pos_tree_singleton p x) pos_leaf
  | xI p => pos_branch None pos_leaf (pos_tree_singleton p x)
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
     | xO p => pos_branch' x (pos_tree_partial_alter' f p l) r
     | xI p => pos_branch' x l (pos_tree_partial_alter' f p r)
     end
  end.

Arguments pos_tree_partial_alter' _ _ !_ !_.

Definition pos_tree_partial_alter (A : Type) (f : option A -> option A)
  (n : positive) (t : pos_tree A) : pos_tree A :=
  pos_tree_partial_alter' f n t.

Arguments pos_tree_partial_alter _ _ _ _ /.

Fixpoint pos_tree_map (A B : Type)
  (f : A -> B) (t : pos_tree A) {struct t} : pos_tree B :=
  match t with
  | pos_leaf => pos_leaf
  | pos_branch x l r => pos_branch (option_map f x)
    (pos_tree_map f l) (pos_tree_map f r)
  end.

Arguments pos_tree_map _ _ _ !_.

(** Replicating sequence A059893. *)

Fixpoint pos_reverse' (n p : positive) {struct p} : positive :=
  match p with
  | xI q => pos_reverse' (xI n) q
  | xO q => pos_reverse' (xO n) q
  | xH => n
  end.

Arguments pos_reverse' _ !_.

Definition pos_reverse (n : positive) : positive := pos_reverse' xH n.

Arguments pos_reverse _ /.

(* Compute map pos_reverse [xH;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16]. *)

Fixpoint pos_tree_to_list' (A : Type)
  (n : positive) (a : list (positive * A)) (t : pos_tree A) {struct t} :
  list (positive * A) :=
  match t with
  | pos_leaf => a
  | pos_branch x l r =>
    let k := pos_tree_to_list' (xO n) (pos_tree_to_list' (xI n) a r) l in
    match x with
    | Some b => cons (n, b) k
    | None => k
    end
  end.

Arguments pos_tree_to_list' _ _ _ !_.

Definition pos_tree_to_list (A : Type) (t : pos_tree A) :
  list (positive * A) :=
  pos_tree_to_list' xH nil t.

Arguments pos_tree_to_list _ !_.

Local Open Scope positive_scope.

(** Merge sort passionately! *)

Program Fixpoint merge' (l0 l1 : list positive)
  {measure (length l0 + length l1)%nat} : list positive :=
  match l0, l1 with
  | nil, _ => l1
  | _, nil => l0
  | cons n0 k0, cons n1 k1 => if n0 <=? n1 then
    cons n0 (merge' k0 l1) else
    cons n1 (merge' l0 k1)
  end.
Next Obligation. intros. subst. cbn in *. lia. Qed.
Next Obligation. intros. subst. cbn in *. lia. Qed.
Next Obligation. Tactics.program_simplify. Qed.

Arguments merge' _ / : simpl nomatch.

Definition merge (l0 l1 : list positive) : list positive := merge' l0 l1.

Arguments merge !_ !_.

Program Fixpoint merge_by' (A : Type) (f : A -> positive) (l0 l1 : list A)
  {measure (length l0 + length l1)%nat} : list A :=
  match l0, l1 with
  | nil, _ => l1
  | _, nil => l0
  | cons n0 k0, cons n1 k1 => if f n0 <=? f n1 then
    cons n0 (merge_by' f k0 l1) else
    cons n1 (merge_by' f l0 k1)
  end.
Next Obligation. intros. subst. cbn in *. lia. Qed.
Next Obligation. intros. subst. cbn in *. lia. Qed.
Next Obligation. Tactics.program_simplify. Qed.

Arguments merge_by' _ _ _ / : simpl nomatch.

Definition merge_by (A : Type) (f : A -> positive) (l0 l1 : list A) :
  list A := merge_by' f l0 l1.

Arguments merge_by _ _ !_ !_.

Fixpoint pos_tree_to_sorted_list' (A : Type)
  (n : positive) (t : pos_tree A) {struct t} : list (positive * A) :=
  match t with
  | pos_leaf => nil
  | pos_branch x l r =>
    let k := merge_by fst
    (pos_tree_to_sorted_list' (xO n) l)
    (pos_tree_to_sorted_list' (xI n) r) in
    match x with
    | Some b => cons (n, b) k
    | None => k
    end
  end.

Arguments pos_tree_to_sorted_list' _ _ !_.

Definition pos_tree_to_sorted_list (A : Type) (t : pos_tree A) :
  list (positive * A) :=
  pos_tree_to_sorted_list' xH t.

Arguments pos_tree_to_sorted_list _ !_.

(** Now we struggle. *)

Definition prod_bimap (A B C D : Type)
  (f : A -> B) (g : C -> D) (x : A * C) : B * D :=
  match x with
  | (a, b) => (f a, g b)
  end.

Arguments prod_bimap _ _ _ _ _ _ !_.

Definition prod_map (A B : Type) (f : A -> B) (x : A * A) : B * B :=
  prod_bimap f f x.

Arguments prod_map _ _ _ _ /.

(** Trichotomy from the Haskell land.
    Actually works in more cases than the tri prefix would have you believe. *)

Local Notation "'LT'" := (inleft (left _))
  (at level 0, no associativity, only parsing).
Local Notation "'EQ'" := (inleft (right _))
  (at level 0, no associativity, only parsing).
Local Notation "'GT'" := (inright _)
  (at level 0, no associativity, only parsing).

Definition pos_trichotomy_inf (p q : positive) : {p < q} + {p = q} + {q < p}.
Proof. decide (p < q); decide (p = q); decide (q < p); auto || lia. Defined.

Definition pos_max (l : list positive) : positive := fold_right max xH l.

Program Fixpoint pos_tree_of_sorted_list' (A : Type)
  (l : list (positive * A)) (n : positive)
  {measure (length l + to_nat (sub (xI (pos_max (map fst l))) n))%nat} :
  pos_tree A :=
  match l with
  | nil => pos_leaf
  | cons (p, x) k =>
    match pos_trichotomy_inf p n with
    | LT => pos_tree_of_sorted_list' k n
    | EQ => pos_branch (Some x)
      (pos_tree_of_sorted_list' k (xO n))
      (pos_tree_of_sorted_list' k (xI n))
    | GT => pos_branch' None
      (pos_tree_of_sorted_list' l (xO n))
      (pos_tree_of_sorted_list' l (xI n))
    end
  end.
(** Structurally recursive cases. *)
Next Obligation. intros. subst. cbv [pos_max]; cbn. lia. Qed.
Next Obligation. intros. subst. cbv [pos_max]; cbn. lia. Qed.
Next Obligation. intros. subst. cbv [pos_max]; cbn. lia. Qed.
(** The tricky bits. *)
Next Obligation.
  intros. subst. cbv [pos_max]; cbn.
  (** Natural number wrangling. *)
  apply Lt.lt_n_S. apply Plus.plus_lt_compat_l.
  apply Pos2Nat.inj_lt.
  (** Decision on positive numbers. *)
  lia. Qed.
(** Repeat with [xI] in place of [xO].
    The measure has [xI] to cancel both cases,
    since [xO n <= xI n] and [xI n <= xI n]. *)
Next Obligation.
  intros. subst. cbv [pos_max]; cbn.
  apply Lt.lt_n_S. apply Plus.plus_lt_compat_l.
  apply Pos2Nat.inj_lt.
  lia. Qed.

(** If this function is given a list that is not sorted,
    its behavior will not be undefined!
    It will merely consider the largest sorted sublist
    (which, like a subsequence, is not necessarily contiguous).
    For example [[(2, 2); (4, 4); (5, 5); (3, 3); (7, 7)]]
    will be treated as [[(2, 2); (4, 4); (5, 5); (7, 7)]]. *)

Definition pos_tree_of_sorted_list (A : Type) (l : list (positive * A)) :
  pos_tree A :=
  pos_tree_of_sorted_list' l xH.

Fixpoint merge_list_to_stack (A : Type)
  (f : A -> positive) (a : list (option (list A))) (l : list A) {struct a} :
  list (option (list A)) :=
  match a with
  | [] => [Some l]
  | None :: a' => Some l :: a'
  | Some l' :: a' =>
    None :: merge_list_to_stack f a' (merge_by f l' l)
  end.

Fixpoint merge_stack (A : Type)
  (f : A -> positive) (a : list (option (list A))) {struct a} : list A :=
  match a with
  | [] => []
  | None :: a' => merge_stack f a'
  | Some l :: a' => merge_by f l (merge_stack f a')
  end.

Fixpoint iter_merge (A : Type)
  (f : A -> positive) (a : list (option (list A))) (l : list A) {struct l} :
  list A :=
  match l with
  | [] => merge_stack f a
  | a' :: l' => iter_merge f (merge_list_to_stack f a [a']) l'
  end.

Definition sort_by (A : Type) (f : A -> positive) (l : list A) :
  list A := iter_merge f nil l.

Arguments sort_by _ _ !_.

Definition pos_tree_of_list (A : Type) (l : list (positive * A)) :
  pos_tree A := pos_tree_of_sorted_list (sort_by fst l).

Fixpoint pos_tree_omap (A B : Type) (f : A -> option B)
  (t : pos_tree A) {struct t} : pos_tree B :=
  match t with
  | pos_leaf => pos_leaf
  | pos_branch x l r =>
    pos_branch' (option_bind f x) (pos_tree_omap f l) (pos_tree_omap f r)
  end.

Fixpoint pos_tree_merge (A B C : Type) (f : option A -> option B -> option C)
  (t0 : pos_tree A) (t1 : pos_tree B) {struct t0} : pos_tree C :=
  match t0, t1 with
  | pos_leaf, t1 => pos_tree_omap (f None o Some) t1
  | t0, pos_leaf => pos_tree_omap (flip f None o Some) t0
  | pos_branch o0 l0 r0, pos_branch o1 l1 r1 =>
    pos_branch' (f o0 o1)
    (pos_tree_merge f l0 l1)
    (pos_tree_merge f r0 r1)
  end.

#[local] Hint Resolve squash : core.

Definition pos_map (A : Type) : Type :=
  {t : pos_tree A $ Squash (pos_tree_wf t)}.

Global Instance Ssig_has_equiv_dec (A : Type) (P : A -> SProp) `(EqDec A) :
  EqDec (Ssig P).
Proof. cbv [EqDec] in *. intros [] []. pose proof H Spr1 Spr0. destruct H0.
  left. apply Spr1_inj. auto.
  right. intros ?. inversion H0. contradiction. Defined.

Global Instance pos_map_has_equiv_dec (A : Type) `(EqDec A) : EqDec (pos_map A).
Proof. typeclasses eauto. Defined.

Program Definition pos_map_empty (A : Type) : pos_map A :=
  Sexists (Squash o pos_tree_wf) pos_leaf _.
Next Obligation. eauto. (* intros A. apply squash. reflexivity. *) Qed.

Definition pos_map_lookup (A : Type)
  (n : positive) (m : pos_map A) : option A :=
  pos_tree_lookup n (Spr1 m).

Set Universe Polymorphism.

Program Definition pos_map_partial_alter (A : Type)
  (f : option A -> option A) (n : positive) (m : pos_map A) : pos_map A :=
  Sexists (Squash o pos_tree_wf) (pos_tree_partial_alter f n (Spr1 m)) _.
Next Obligation.
  intros A f n [t w]. apply squash. cbn -[pos_tree_wf].
  pose proof unsquash w as w'. clear w. rename w' into w.
  induction t.
    cbv [pos_tree_partial_alter pos_tree_partial_alter']. destruct (f None).
    apply pos_tree_wf_singleton.
    reflexivity.
    pose proof pos_tree_wf_l _ _ _ w as wl.
    pose proof pos_tree_wf_r _ _ _ w as wr.
    apply IHt1 in wl.
    apply IHt2 in wr. Admitted.

Definition pos_map_insert (A : Type)
  (n : positive) (a : A) (m : pos_map A) : pos_map A :=
  pos_map_partial_alter (fun _ : option A => Some a) n m.

Lemma option_map_Some (A B : Type) (f : A -> B) (x : option A) (b : B)
  (e : option_map f x = Some b) : {a : A | x = Some a /\ b = f a}.
Proof.
  cbv [option_map] in e. destruct x as [a |].
  - inversion e as [e']. exists a. auto.
  - inversion e. Qed.

Lemma option_map_None (A B : Type) (f : A -> B) (x : option A)
  (e : option_map f x = None) : x = None.
Proof.
  cbv [option_map] in e. destruct x as [a |].
  - congruence.
  - reflexivity. Qed.

Program Definition pos_map_map (A B : Type)
  (f : A -> B) (m : pos_map A) : pos_map B :=
  Sexists (Squash o pos_tree_wf) (pos_tree_map f (Spr1 m)) _.
Next Obligation. intros A B f [t w]. apply squash. cbn.
  pose proof unsquash w as w'. clear w. rename w' into w.
  induction t.
    cbv [pos_tree_map]. assumption.
    pose proof pos_tree_wf_l _ _ _ w as wl.
    pose proof pos_tree_wf_r _ _ _ w as wr.
    apply IHt1 in wl.
    apply IHt2 in wr.
    destruct x, t1, t2; auto.
    apply pos_tree_wf_branch; auto.
    apply pos_tree_wf_branch; auto.
    cbn [option_map].
    cbn; auto with bool.
    cbn; auto with bool. Qed.

Arguments pos_map_map _ _ _ !_.

Definition pos_map_to_list (A : Type) (m : pos_map A) : list (positive * A) :=
  pos_tree_to_list (Spr1 m).

Definition pos_map_to_sorted_list (A : Type)
  (m : pos_map A) : list (positive * A) :=
  pos_tree_to_sorted_list (Spr1 m).

Program Definition pos_map_omap (A B : Type) (f : A -> option B)
  (m : pos_map A) : pos_map B :=
  Sexists (Squash o pos_tree_wf) (pos_tree_omap f (Spr1 m)) _.
Next Obligation. intros A B f [t w]. apply squash. cbn.
  pose proof unsquash w as w'. clear w. rename w' into w.
  Admitted.

Program Definition pos_map_merge (A B C : Type)
  (f : option A -> option B -> option C)
  (m0 : pos_map A) (m1 : pos_map B) : pos_map C :=
  Sexists (Squash o pos_tree_wf) (pos_tree_merge f (Spr1 m0) (Spr1 m1)) _.
Next Obligation. intros A B C f [t0 w0] [t1 w1]. apply squash. cbn. Admitted.

Definition pos_map_ifoldr (A B : Type)
  (f : positive -> A -> B -> B) (b : B) (m : pos_map A) : B :=
  fold_right (prod_uncurry f) b (pos_map_to_sorted_list m).

Definition pos_map_forall (A : Type) (P : A -> Prop) (m : pos_map A) : Prop :=
  forall (n : positive) (x : A), pos_map_lookup n m = Some x -> P x.

Definition pos_map_iforall (A : Type) (P : positive -> A -> Prop)
  (m : pos_map A) : Prop :=
  forall (n : positive) (x : A), pos_map_lookup n m = Some x -> P n x.

(* Has.Coding *)

(** Coding. *)

Class HasCode (A B : Type) : Type := code : (A -> option B) * (B -> A).

Typeclasses Transparent HasCode.

#[local] Hint Mode HasCode - - : typeclass_instances.

(* Provides.TwoSorted.CodeMappings *)

Section Context.

Context (A B : Type) `(HasCode A B).

(** Decoding. *)

Definition decode : A -> option B := fst code.

(** Encoding. *)

Definition encode : B -> A := snd code.

End Context.

Arguments decode {_ _ !_} _.
Arguments encode {_ _ !_} _.

(* Is.OneSorted.Countable *)

(** Change [N] here and then lift the [positive] properties,
    just like in the standard library. *)

Class IsCnt (A : Type) `(HasCode positive A) : Prop := {
  decode_encode : forall x : A, decode (encode x) = Some x;
  (* encode_decode : forall n : positive,
    option_map encode (decode n) = Some n; *)
  lower_subset : forall n p : positive, p < n ->
    is_Some (decode n) -> is_Some (decode p);
}.

Arguments IsCnt _ {_}.

Global Instance positive_positive_has_code : HasCode positive positive :=
  (Some, id).

Global Instance positive_is_cnt : IsCnt positive.
Proof. split; auto. Qed.

Global Instance positive_prod_has_code :
  HasCode positive (positive * positive) :=
  (Some o s_pair, prod_uncurry s_unpair).

(* Global Instance prod_has_code (A : Type) `(HasCode positive A) :
  HasCode positive (A * A) :=
  (pair_option o prod_map decode o pair_diag, encode o prod_map encode). *)

Global Instance prod_has_code (A B : Type)
  `(HasCode positive A) `(HasCode positive B) :
  HasCode positive (A * B) :=
  (pair_option o prod_bimap decode decode o pair_diag,
  encode o prod_bimap encode encode).

(* Global Instance prod_is_cnt (A : Type) `(IsCnt A) : IsCnt (A * A).
Proof. split. intros [n p]. Admitted. *)

Global Instance prod_is_cnt (A B : Type) `(IsCnt A) `(IsCnt B) : IsCnt (A * B).
Proof. split. intros [n p]. Admitted.

Section Context.

Context (K : Type) `{IsCnt K}.

Definition fin_map_wf (A : Type) (m : pos_map A) :=
  pos_map_iforall (fun (n : positive) (_ : A) =>
    option_map (A := K) (B := positive) encode (decode n) = Some n) m.

Definition fin_map (A : Type) : Type :=
  {m : pos_map A $ Squash (fin_map_wf m)}.

End Context.

Arguments fin_map _ {_} _.

Section Context.

Context (K : Type) `{IsCnt K}.

Definition fin_map_to_sorted_list (A : Type)
   (m : fin_map K A) : list (K * A) :=
  list_omap (fst_option o prod_bimap decode id)
  (pos_map_to_sorted_list (Spr1 m)).

Definition fin_map_ifoldr (A B : Type)
  (f : K -> A -> B -> B) (b : B) (m : fin_map K A) : B :=
  fold_right (prod_uncurry f) b (fin_map_to_sorted_list m).

Program Definition fin_map_empty (A : Type) : fin_map K A :=
  Sexists (Squash o fin_map_wf) (pos_map_empty A) _.
Next Obligation. intros A. apply squash. intros n a e. inversion e. Qed.

Program Definition fin_map_partial_alter (A : Type)
  (f : option A -> option A) (n : K) (m : fin_map K A) : fin_map K A :=
  Sexists (Squash o fin_map_wf)
  (pos_map_partial_alter f (encode n) (Spr1 m)) _.
Next Obligation. Admitted.

Definition fin_map_insert (A : Type)
  (n : K) (a : A) (m : fin_map K A) : fin_map K A :=
  fin_map_partial_alter (fun _ : option A => Some a) n m.

End Context.

Section Context.

Context (K L : Type) `{IsCnt K} `{IsCnt L}.

(** Finally, we can define the ordered left Kan extension along inclusion. *)

Definition fin_map_free_lan (A : Type)
  (h : K -> L) (m : fin_map K A) : fin_map L (list A) :=
  fin_map_ifoldr (fun (n : K) (a : A) (m' : fin_map L (list A)) =>
    fin_map_partial_alter (fun x : option (list A) =>
      Some (a :: option_extract [] x)) (h n) m') (fin_map_empty (list A)) m.

(** Also, the free product without tears. *)

Definition fin_map_free_prod (A B : Type)
  (m0 : fin_map K A) (m1 : fin_map L B) : fin_map (K * L) (A * B) :=
  fin_map_ifoldr (fun (i : K) (a : A) (z : fin_map (K * L) (A * B)) =>
    fin_map_ifoldr (fun (j : L) (b : B) (z : fin_map (K * L) (A * B)) =>
      fin_map_insert (i, j) (a, b) z) z m1) (fin_map_empty (A * B)) m0.

End Context.

Definition pos_map_free_lan (A : Type)
  (h : positive -> positive) (m : pos_map A) : pos_map (list A) :=
  pos_map_ifoldr (fun (n : positive) (a : A) (m' : pos_map (list A)) =>
    pos_map_partial_alter (fun x : option (list A) =>
      Some (a :: option_extract [] x)) (h n) m') (pos_map_empty (list A)) m.

(** The scopes are messed up. *)

Lemma pos_map_free_lan_nonempty (A : Type)
  (h : positive -> positive) (m : pos_map A) :
  pos_map_forall (not o Logic.eq []) (pos_map_free_lan h m).
Proof. Admitted.

Definition cut_map_wf (A : Type) (P : A -> Prop) (m : pos_map A) : Prop :=
  pos_map_forall (not o P) m.

(* Arguments cut_map_wf _ _ !_. *)

Definition cut_map (A : Type) (P : A -> Prop) : Type :=
  {m : pos_map A $ Squash (cut_map_wf P m)}.

Lemma Unnamed_goal (A : Type) (P : A -> Prop) (x y : cut_map P) :
  x = y <-> Spr1 x = Spr1 y.
Proof. destruct x, y; cbn. split. intros. inversion H. auto.
  intros w. apply Spr1_inj. cbn. auto. Qed.

(** We can now represent polynomials with [cut_map (eq 0)]. *)

Definition dec_map_wf (A : Type) (p : A -> bool) (m : pos_map A) : Prop :=
  pos_map_forall (is_true o p) m.

(* Arguments dec_map_wf _ _ !_. *)

Definition dec_map (A : Type) (p : A -> bool) : Type :=
  {m : pos_map A $ Squash (dec_map_wf p m)}.

Lemma Unnamed_goal' (A : Type) (p : A -> bool) (x y : dec_map p) :
  x = y <-> Spr1 x = Spr1 y.
Proof. destruct x, y; cbn. split. intros. inversion H. auto.
  intros w. apply Spr1_inj. cbn. auto. Qed.

(** We can now represent polynomials over discrete rings
    with [dec_map (eqb 0)] or [dec_map (is_left o dec o eq 0)]. *)
