(* bad *)

Set Warnings "-ambiguous-paths".

From Coq Require Import
  ZArith.ZArith.
From stdpp Require Import
  option finite fin_maps gmap gmultiset pmap.
From Maniunfold.Has Require Export
  Unsquashing
  OneSortedEnumeration OneSortedCardinality.
From Maniunfold.Is Require Export
  OneSortedFinite Isomorphism
  Ring TwoSortedUnitalAssociativeAlgebra TwoSortedGradedAlgebra.
From Maniunfold.Is Require Export
  OneSortedAbelianGroup Semigroup
  Monoid OneSortedSemiring
  Ring.
From Maniunfold.Offers Require Export
  OneSortedPositiveOperations OneSortedNaturalOperations
  OneSortedIntegerOperations.
From Maniunfold.Provides Require Export
  NTheorems ZTheorems.
From Maniunfold.ShouldHave Require
  OneSortedAdditiveNotations OneSortedMultiplicativeNotations.
From Maniunfold.ShouldHave Require
  OneSortedArithmeticNotations.
From Maniunfold.ShouldOffer Require
  OneSortedArithmeticOperationNotations.

Generalizable All Variables.

Global Instance this_thing `(HasEqDec A) : EqDecision A.
Proof.
  intros x y.
  decide (x = y) as [e | f].
  - left. apply e.
  - right. apply f. Qed.

#[local] Arguments decide : simpl never.

Section more_merge.

Context `{FinMap K M}.

Context {A B C : Type} {f : option A → option B → option C} `{!DiagNone f}.

(** TODO Ask the std++ people about merging this. *)

Lemma insert_merge_None (m1 : M A) (m2 : M B) i y z :
  f (Some y) (Some z) = None ->
  delete i (merge f m1 m2) = merge f (<[i:=y]> m1) (<[i:=z]> m2).
Proof. by intros; apply partial_alter_merge. Qed.

End more_merge.

Definition dom_partial_alter {K A M : Type} `{PartialAlter K A M}
  (f : option A -> A) (i : K) (m : M) : M :=
  partial_alter (fun x : option A => mret (f x)) i m.

Definition codom_partial_alter {K A M : Type} `{PartialAlter K A M}
  (f : A -> option A) (i : K) (m : M) : M :=
  partial_alter (fun x : option A => mbind f x) i m.

(** Indexed mapping. *)

Definition map_imap {K A B MA MB : Type}
  `{FinMapToList K A MA} `{Insert K B MB} `{Empty MB}
  (f : K -> A -> B) (m : MA) : MB :=
  map_fold (fun (k : K) (a : A) => insert k (f k a)) empty m.

Section Context.

Context `{FinMap K M}.

Lemma map_imap_empty {A B : Type} (f : K -> A -> B) :
  map_imap (MA := M A) (MB := M B) f empty = empty.
Proof with auto.
  cbv [map_imap]. rewrite map_fold_empty... Qed.

Lemma map_imap_singleton {A B : Type} (f : K -> A -> B) (k : K) (a : A) :
  map_imap (MA := M A) (MB := M B) f (singletonM k a) = singletonM k (f k a).
Proof with auto.
  cbv [map_imap]. do 2 rewrite <- insert_empty. rewrite map_fold_insert_L.
  - rewrite map_fold_empty...
  - intros. rewrite insert_commute...
  - rewrite lookup_empty... Qed.

End Context.

Example peemap_raw : Pmap_raw nat.
Proof.
  apply PNode.
  - apply None.
  - apply PNode.
    + apply Some. apply 42.
    + apply PLeaf.
    + apply PLeaf.
  - apply PNode.
    + apply Some. apply 13.
    + apply PNode.
      * apply Some. apply 7.
      * apply PLeaf.
      * apply PLeaf.
    + apply PLeaf. Defined.

Example peemap : Pmap nat.
Proof. apply (PMap peemap_raw I). Defined.

(** The std++ documentation says that
    the order of the return value of [map_to_list] is unspecified,
    but this is silly, because [Pmap] is inherently ordered. *)

Example peelist : list (positive * nat) := map_to_list peemap.

(** Left Kan extension of finitely-supported functions along inclusion,
    where the commutative monoid is free.
    It would be nicer to use a list instead of a multiset,
    since the domain of maps ought to be ordered anyway and
    countability of values is not essential,
    but this is not afforded to us by the map interface. *)

Definition map_free_lan {K L A MK ML : Type}
  `{Countable A} `{FinMapToList K A MK}
  `{Empty ML} `{PartialAlter L (gmultiset A) ML}
  (p : K -> L) (m : MK) : ML :=
  map_fold (fun (i : K) (x : A) (n : ML) =>
    partial_alter (fun a : option (gmultiset A) =>
      Some (base.union (singleton x) (default empty a))) (p i) n) empty m.

Definition map_free_lan' {K L A MK ML : Type}
  `{FinMapToList K A MK} `{Empty ML} `{PartialAlter L (list A) ML}
  (p : K -> L) (m : MK) : ML :=
  map_fold (fun (i : K) (x : A) (n : ML) =>
    partial_alter (fun a : option (list A) =>
      Some (x :: default [] a)) (p i) n) empty m.

(** Left Kan extension of finitely-supported functions along inclusion,
    where the commutative monoid is given (in [f] and [x] pieces).
    It must be commutative and associative, because the fold is unordered;
    it must be unital, because the integration must start somewhere. *)

Definition map_lan {K L A MK ML : Type}
  `{FinMapToList K A MK} `{Empty ML} `{PartialAlter L A ML}
  (f : A -> A -> A) (x : A) (p : K -> L) (m : MK) : ML :=
  map_fold (fun (i : K) (y : A) (n : ML) =>
    partial_alter (fun a : option A =>
      Some (f y (default x a))) (p i) n) empty m.

(** Free product of two finite maps along their keys. *)

Definition map_free_prod {KA KB A B MA MB MAB : Type}
  `{FinMapToList KA A MA} `{FinMapToList KB B MB}
  `{Empty MAB} `{Insert (KA * KB) (A * B) MAB}
  (x : MA) (y : MB) : MAB :=
  map_fold (fun (i : KA) (a : A) (z : MAB) =>
    map_fold (fun (j : KB) (b : B) (z : MAB) =>
      insert (i, j) (a, b) z) z y) empty x.

(** A finite map is equivalent to a function with finite support.
    Almost, at least. We also need an upper bound for the largest key. *)

Definition almost_maplike {K A : Type} `{HasZero A} : Type :=
  {f : K -> A | exists `(Finite J), forall project : J -> K,
    forall i : K, ~ (exists j : J, project j = i) -> f i = zero}.

Definition actually_maplike {K A : Type} `{Finite K} `{HasZero A} : Type :=
  K -> A.

Section Context.

Lemma filter_fmap {A B : Type} {M : Type -> Type}
  `{FMap M} `{Filter A (M A)} `{Filter B (M B)}
  (P : A -> Prop) `{forall x : A, Decision (P x)}
  (f : B -> A) `{forall x : B, Decision (compose P f x)} (xs : M B) :
  filter P (f <$> xs) = f <$> filter (compose P f) xs.
Proof. Abort.

Context `{FinMap K M} `{FinMap L M'}.

Lemma map_free_lan_fmap {A B : Type} (p : K -> L) (f : A -> B) (x : M A) :
  fmap f <$> map_free_lan' p x = map_free_lan' p (f <$> x).
Proof. Admitted.

Lemma map_Forall_free_lan {A : Type} {P : L -> A -> Prop}
  (p : K -> L) (x : M A) :
  map_Forall (fun (i : K) (a : A) => P (p i) a) x <->
  map_Forall (fun (i : L) (a : list A) => Forall (P i) a)
  (map_free_lan' (MK := M A) (ML := M' (list A)) p x).
Proof. Admitted.

Lemma map_Forall_free_lan_const {A : Type} {P : A -> Prop}
  (p : K -> L) (x : M A) :
  map_Forall (const P) x <->
  map_Forall (const (Forall P))
  (map_free_lan' (MK := M A) (ML := M' (list A)) p x).
Proof. exact (map_Forall_free_lan p x). Defined.

(** If we wish to state that [map_free_prod] is associative,
    we need to transport one side of the equation via [assoc] on [prod].
    However, inhabiting this instance of [assoc] requires univalence.
    We could also express the property pointwise,
    but that still requires pointwise transport with [fmap].
    More generally, [map_free_prod] is free,
    so it commutes with all the obvious things. *)

(* Lemma map_free_prod_fmap {A B A' B' : Type}
  (f : A -> A') (g : B -> B') (x : M A) (y : M' B) :
  prod_map f g <$> map_free_prod x y = map_free_prod (f <$> x) (g <$> y).
Proof. Admitted. *)

End Context.

Section Context.

Import OneSortedArithmeticNotations.

Definition map_sum {K A M : Type}
  `{FinMapToList K A M} `{HasAdd A} `{HasZero A}
  (m : M) : A := map_fold (const _+_) 0 m.

Definition map_product {K A M : Type}
  `{FinMapToList K A M} `{HasMul A} `{HasOne A}
  (m : M) : A := map_fold (const _*_) 1 m.

Definition set_sum {A M : Type}
  `{Elements A M} `{HasAdd A} `{HasZero A}
  (m : M) : A := set_fold _+_ 0 m.

Definition set_product {A M : Type}
  `{Elements A M} `{HasMul A} `{HasOne A}
  (m : M) : A := set_fold _*_ 1 m.

Definition list_sum {A : Type}
  `{HasAdd A} `{HasZero A}
  (l : list A) : A := foldr _+_ 0 l.

Definition list_product {A : Type}
  `{HasMul A} `{HasOne A}
  (l : list A) : A := foldr _*_ 1 l.

End Context.

(** TODO Uh oh! *)

Notation "'`' x" := (Spr1 x).

Section Context.

Import OneSortedArithmeticNotations.
Import OneSortedArithmeticOperationNotations.

Context (A : Type) `{IsRing A} `{HasEqDec A} `{Countable A}.

(** We cannot keep zero values in the map,
    because they would break definitional equality and
    needlessly increase space usage. *)

Definition poly_value_wf (n : N) (a : A) : Prop := a <> 0.
Definition poly_wf (m : gmap N A) : Prop := map_Forall poly_value_wf m.
Definition poly : Type := Ssig (fun m : gmap N A => Squash (poly_wf m)).

Lemma poly_lookup_wf : forall (x : poly) (i : N),
  `x !! i <> Some 0.
Proof.
  intros [x Wp] i. intros Hyp.
  pose proof unsquash Wp as Wp'.
  pose proof map_Forall_lookup_1 poly_value_wf x i 0 Wp' Hyp as Wc.
  apply Wc. reflexivity. Defined.

Ltac stabilize :=
  repeat match goal with
  | H : ~ ?a <> ?b |- _ => apply dec_stable in H
  end.

Import Addition.Subclass Zero.Subclass Negation.Subclass
  Multiplication.Subclass One.Subclass.

Ltac conversions := typeclasses
  convert bin_op into (add (A := poly)) and
  null_op into (zero (A := poly)) and
  un_op into (neg (A := poly)) or
  convert bin_op into (mul (A := poly)) and
  null_op into (one (A := poly)) or
  convert bin_op into (add (A := A)) and
  null_op into (zero (A := A)) and
  un_op into (neg (A := A)) or
  convert bin_op into (mul (A := A)) and
  null_op into (one (A := A)).

Definition poly_value_eval (x : A) (n : N) (a : A) : A := a * (x ^ n)%N.

Definition poly_eval (p : poly) (x : A) : A :=
  map_sum (map_imap (MB := gmap N A) (poly_value_eval x) (`p)).

(** Addition of polynomials.

    The terms of the polynomials $x$, $y$ and $z$ in $z = x + y$
    are related by the parallel summation $z_n = x_n + y_n$ for all $n$.
    We need to prune zero terms after carrying out each addition,
    because it is possible that $z_n = 0$ for some $n$,
    even though $x_n \ne 0$ and $y_n \ne 0$;
    indeed, this happens whenever $y_n = - x_n$. *)

Program Definition poly_add (x y : poly) : poly :=
  Sexists (Squash o poly_wf) (union_with (fun a b : A => let c := a + b in
    if decide (c <> 0) then Some c else None) (`x) (`y)) _.
Next Obligation.
  intros x y. apply squash.
  intros i a Hyp. intros Ha. subst a.
  apply lookup_union_with_Some in Hyp. cbn in Hyp.
  destruct Hyp as [[hx hy] | [[hx hy] | [a [b [hx [hy hxy]]]]]].
  - apply (poly_lookup_wf x i hx).
  - apply (poly_lookup_wf y i hy).
  - decide (a + b <> 0) as [fab | fab]; stabilize.
    + inversion hxy as [hab]. apply fab. apply hab.
    + inversion hxy. Defined.

(** Zero polynomial.

    The terms of the polynomial $x$ in $x = 0$
    are constrained by $x_n = 0$ for all $n$. *)

Program Definition poly_zero : poly := Sexists (Squash o poly_wf) empty _.
Next Obligation.
  apply squash.
  intros i a Hyp. intros Ha. subst a.
  apply lookup_empty_Some in Hyp.
  destruct Hyp. Defined.

(** Negation of polynomials.

    The terms of the polynomials $x$ and $y$ in $y = - x$
    are related by the pointwise negation $y_n = - x_n$ for all $n$. *)

Program Definition poly_neg (x : poly) : poly :=
  Sexists (Squash o poly_wf) (neg <$> `x) _.
Next Obligation with conversions.
  intros x. apply squash.
  intros i a Hyp. intros Ha. subst a.
  rewrite lookup_fmap in Hyp.
  pose proof fmap_Some_1 _ _ _ Hyp as Hyp'.
  destruct Hyp' as [a [hx hy]].
  rewrite <- (fixed (x := 0) (f := -_)) in hy. apply inj in hy. subst a.
  apply (poly_lookup_wf x i hx). Defined.

(** Multiplication of polynomials.

    The terms of the polynomials $x$, $y$ and $z$ in $z = x \times y$
    are related by the discrete convolution
    $r_q = \sum_{n + p = q} x_n \times y_p$ for all $n$, $p$ and $q$.
    We need to prune the terms after carrying out each addition,
    because it is possible that $z_q = 0$ for some $q$,
    as was the case with $x + y$. *)

Program Definition poly_mul (x y : poly) : poly :=
  Sexists (Squash o poly_wf) (filter (prod_uncurry poly_value_wf)
    (set_sum <$> map_free_lan (prod_uncurry add (A := N))
      (prod_uncurry mul <$> map_free_prod (`x) (`y)))) _.
Next Obligation.
  intros x y. apply squash.
  intros i a Hyp. intros Ha. subst a.
  apply map_filter_lookup_Some in Hyp.
  destruct Hyp as [Hyp Wc].
  apply Wc. reflexivity. Defined.

Program Definition poly_mul' (x y : poly) : poly :=
  Sexists (Squash o poly_wf) (filter (prod_uncurry poly_value_wf)
    (map_lan (add (A := A)) 0 (prod_uncurry add (A := N))
      (prod_uncurry mul <$> map_free_prod (`x) (`y)))) _.
Next Obligation. Admitted.

(** Unit polynomial.

    The terms of the polynomial $x$ in $x = 1$
    are constrained by $x_0 = 1$ and $x_n = 0$ for all $n > 0$. *)

Program Definition poly_one : poly :=
  Sexists (Squash o poly_wf)
  (if decide (1 <> 0) then singletonM 0 1 else empty) _.
Next Obligation.
  apply squash.
  intros i a Hyp. intros Ha. subst a.
  decide (1 <> 0) as [F10 | F10]; stabilize.
  - rewrite lookup_singleton_ne in Hyp.
    + inversion Hyp.
    + intros Hi. subst i.
      rewrite lookup_singleton in Hyp. inversion Hyp as [H10].
      apply F10. apply H10.
  - rewrite lookup_empty in Hyp. inversion Hyp. Defined.

(** We could use the zero-product property to speed up computations here,
    but not fully, because our ring may not be a domain. *)

(** Left scalar multiplication of polynomials.

    The scalar $a$ and
    the terms of the polynomials $x$ and $y$ in $y = a \times x$
    are related by the pointwise multiplication
    $x_n = a \times x_n$ for all $n$. *)

Program Definition poly_act_l (a : A) (x : poly) : poly :=
  Sexists (Squash o poly_wf)
  (filter (prod_uncurry poly_value_wf) (mul a <$> `x)) _.
Next Obligation with conversions.
  intros a x. apply squash.
  intros i b Hyp. intros Hb. subst b.
  apply map_filter_lookup_Some in Hyp.
  destruct Hyp as [Hyp Wc].
  apply Wc. reflexivity. Defined.

(** Right scalar multiplication of polynomials.

    The scalar $a$ and
    the terms of the polynomials $x$ and $y$ in $y = x \times a$
    are related by the pointwise multiplication
    $x_n = x_n \times a$ for all $n$. *)

Program Definition poly_act_r (x : poly) (a : A) : poly :=
  Sexists (Squash o poly_wf)
  (filter (prod_uncurry poly_value_wf) (flip mul a <$> `x)) _.
Next Obligation with conversions.
  intros a x. apply squash.
  intros i b Hyp. intros Hb. subst b.
  apply map_filter_lookup_Some in Hyp.
  destruct Hyp as [Hyp Wc].
  apply Wc. reflexivity. Defined.

End Context.

(* Section Tests.

Local Open Scope N_scope.
Local Open Scope Z_scope.

(* 42 * x ^ 3 + 7 + 13 * x *)
Program Let p : poly := exist poly_wf
  (insert 3%N 42%Z (insert 0%N 7%Z (insert 1%N 13%Z empty))) _.
Next Obligation. Admitted.

(* 3 * x ^ 4 + x + 5 *)
Program Let q : poly := exist poly_wf
  (insert 4%N 3%Z (insert 1%N 1%Z (insert 0%N 5%Z empty))) _.
Next Obligation. Admitted.

Compute map_to_list (``(poly_mul p q)).

(* 7, 5 *)
Compute poly_eval p 0.
Compute poly_eval q 0.

(* 1180, 251 *)
Compute poly_eval p 3.
Compute poly_eval q 3.

(* None, PLeaf *)
(* Compute poly_add p (poly_neg p).
Compute poly_add (poly_neg q) q. *)

(* 12, 1431 *)
Compute poly_eval (poly_add p q) 0.
Compute poly_eval (poly_add p q) 3.

(* 35, 296180 *)
Compute poly_eval (poly_mul p q) 0.
Compute poly_eval (poly_mul p q) 3.

End Tests. *)

Module Additive.

Import OneSortedAdditiveNotations.
Import OneSortedArithmeticNotations.

Section Context.

Context (A : Type) `{IsRing A} `{HasEqDec A}.

(** Performing this specialization by hand aids type inference. *)

Let poly := poly (A := A).

Import Addition.Subclass Zero.Subclass Negation.Subclass
  Multiplication.Subclass One.Subclass.

Ltac conversions := typeclasses
  convert bin_op into (add (A := poly)) and
  null_op into (zero (A := poly)) and
  un_op into (neg (A := poly)) or
  convert bin_op into (mul (A := poly)) and
  null_op into (one (A := poly)) or
  convert bin_op into (add (A := A)) and
  null_op into (zero (A := A)) and
  un_op into (neg (A := A)) or
  convert bin_op into (mul (A := A)) and
  null_op into (one (A := A)).

Ltac stabilize :=
  repeat match goal with
  | H : ~ ?a <> ?b |- _ => apply dec_stable in H
  end.

Global Instance poly_has_bin_op : HasBinOp poly := poly_add.
Global Instance poly_has_null_op : HasNullOp poly := poly_zero.
Global Instance poly_has_un_op : HasUnOp poly := poly_neg.

Global Instance poly_bin_op_is_mag : IsMag poly_add.
Proof. Defined.

Global Instance poly_bin_op_is_assoc : IsAssoc poly_add.
Proof with conversions.
  intros x y z.
  cbv [bin_op poly_has_bin_op poly_add]. cbn.
  apply Spr1_inj. cbn.
  cbv [union_with map_union_with].
  match goal with
  |- merge ?e _ _ = merge ?e _ _ => set (f := e)
  end.
  apply (merge_assoc f).
  intros i.
  destruct (`x !! i) as [a |] eqn : Dx,
  (`y !! i) as [b |] eqn : Dy, (`z !! i) as [c |] eqn : Dz; try (
    cbv [f]; replace option_union_with with (union_with (M := option A));
    repeat (rewrite union_with_left_id || rewrite union_with_right_id);
    reflexivity).
  cbv [f].
  cbv [union_with option_union_with].
  decide (a + b <> 0) as [Fab | Fab];
  decide (b + c <> 0) as [Fbc | Fbc]; stabilize; cbn.
  - decide (a + (b + c) <> 0) as [Fa_bc | Fa_bc];
    decide ((a + b) + c <> 0) as [Fab_c | Fab_c]; stabilize; cbn.
    + f_equal. rewrite assoc... reflexivity.
    + exfalso. apply Fa_bc. rewrite assoc... apply Fab_c.
    + exfalso. apply Fab_c. rewrite <- assoc... apply Fa_bc.
    + reflexivity.
  - decide ((a + b) + c <> 0) as [Fab_c | Fab_c];
    stabilize; cbn.
    + f_equal. rewrite <- assoc... rewrite Fbc. rewrite unl_bin_op_r. reflexivity.
    + exfalso. rewrite <- assoc in Fab_c...
      rewrite Fbc in Fab_c. rewrite unl_bin_op_r in Fab_c.
      subst a. apply (poly_lookup_wf x i). apply Dx.
  - decide (a + (b + c) <> 0) as [Fa_bc | Fa_bc];
    stabilize; cbn.
    + f_equal. rewrite assoc... rewrite Fab. rewrite unl_bin_op_l. reflexivity.
    + exfalso. rewrite assoc in Fa_bc...
      rewrite Fab in Fa_bc. rewrite unl_bin_op_l in Fa_bc.
      subst c. apply (poly_lookup_wf z i). apply Dz.
  - f_equal. assert (Ha : a = a + (b + - b)).
    { rewrite inv_r. rewrite unl_bin_op_r. reflexivity. }
    assert (Hc : c = (- b + b) + c).
    { rewrite inv_l. rewrite unl_bin_op_l. reflexivity. }
    rewrite Ha. rewrite assoc...
    rewrite Fab. rewrite unl_bin_op_l.
    rewrite Hc. rewrite <- assoc...
    rewrite Fbc. rewrite unl_bin_op_r. reflexivity. Defined.

Global Instance poly_bin_op_is_semigrp : IsSemigrp poly_add.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_is_comm : IsComm poly_add.
Proof with conversions.
  intros x y. cbv [bin_op poly_has_bin_op poly_add].
  cbv [union_with map_union_with].
  apply Spr1_inj. cbn.
  match goal with
  |- merge ?e _ _ = merge ?e _ _ => set (f := e)
  end.
  apply (merge_comm f).
  intros i.
  destruct (`x !! i) as [a |] eqn : Dx,
  (`y !! i) as [b |] eqn : Dy; try reflexivity.
  cbv [f].
  cbv [union_with option_union_with].
  decide (a + b <> 0) as [Fab | Fab];
  decide (b + a <> 0) as [Fba | Fba]; stabilize; cbn.
  - f_equal. rewrite comm... reflexivity.
  - exfalso. apply Fab. rewrite comm... apply Fba.
  - exfalso. apply Fba. rewrite comm... apply Fab.
  - reflexivity. Defined.

Global Instance poly_bin_op_is_comm_semigrp : IsCommSemigrp poly_add.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_is_unl_l : IsUnlBinOpL null_op poly_add.
Proof.
  intros x. cbv [bin_op poly_has_bin_op poly_add
  null_op poly_has_null_op poly_zero].
  cbv [union_with map_union_with].
  Fail apply (left_id empty (merge (option_union_with _))). Admitted.

Global Instance poly_bin_op_null_op_is_unl_r : IsUnlBinOpR null_op poly_add.
Proof.
  intros x. cbv [bin_op poly_has_bin_op poly_add
  null_op poly_has_null_op poly_zero].
  cbv [union_with map_union_with].
  Fail apply (right_id empty (merge (option_union_with _))). Admitted.

Global Instance poly_bin_op_null_op_is_unl : IsUnlBinOpLR null_op poly_add.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_is_mon : IsMon null_op poly_add.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_is_comm_mon :
  IsCommMon poly_add null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_un_op_is_inv_l_hom :
  IsInvL null_op un_op poly_add.
Proof.
  intros x. cbv [bin_op poly_has_bin_op poly_add
  null_op poly_has_null_op poly_zero
  un_op poly_has_un_op poly_neg].
  cbv [union_with map_union_with]. Admitted.

Global Instance poly_bin_op_null_op_un_op_is_inv_r_hom :
  IsInvR null_op un_op poly_add.
Proof.
  intros x. cbv [bin_op poly_has_bin_op poly_add
  null_op poly_has_null_op poly_zero
  un_op poly_has_un_op poly_neg].
  cbv [union_with map_union_with]. Admitted.

Global Instance poly_bin_op_null_op_un_op_is_inv_hom :
  IsInvLR null_op un_op poly_add.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_un_op_is_grp :
  IsGrp null_op un_op poly_add.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_un_op_is_ab_grp :
  IsAbGrp poly_add null_op un_op.
Proof. split; typeclasses eauto. Defined.

End Context.

End Additive.

Module Multiplicative.

Import OneSortedMultiplicativeNotations.
Import OneSortedArithmeticNotations.

Section Context.

Context (A : Type) `{IsRing A} `{HasEqDec A} `{Countable A}.

Let poly := poly (A := A).

Import Addition.Subclass Zero.Subclass Negation.Subclass
  Multiplication.Subclass One.Subclass.

Ltac conversions := typeclasses
  convert bin_op into (add (A := poly)) and
  null_op into (zero (A := poly)) and
  un_op into (neg (A := poly)) or
  convert bin_op into (mul (A := poly)) and
  null_op into (one (A := poly)) or
  convert bin_op into (add (A := A)) and
  null_op into (zero (A := A)) and
  un_op into (neg (A := A)) or
  convert bin_op into (mul (A := A)) and
  null_op into (one (A := A)).

Global Instance poly_has_bin_op : HasBinOp poly := poly_mul.
Global Instance poly_has_null_op : HasNullOp poly := poly_one.

Global Instance poly_bin_op_is_mag : IsMag poly_mul.
Proof. Defined.

Global Instance poly_bin_op_is_assoc : IsAssoc poly_mul.
Proof with conversions.
  intros x y z.
  cbv [bin_op poly_has_bin_op poly_mul]. cbn.
  apply Spr1_inj. cbn.
  match goal with
  |- filter ?e _ = filter ?e _ => set (P := e)
  end.
  set (f (x y : gmap N A) :=
    filter P
    (set_sum <$>
      map_free_lan (K := N * N) (L := N) (prod_uncurry add)
        (prod_uncurry mul <$>
          map_free_prod x y)) : gmap N A).
  enough (f (`x) (f (`y) (`z)) = f (f (`x) (`y)) (`z)) by assumption.
  destruct x as [m Wm]. cbn.
  generalize dependent m. Admitted.

Global Instance poly_bin_op_is_semigrp : IsSemigrp poly_mul.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_is_comm : IsComm poly_mul.
Proof.
  intros x y.
  cbv [bin_op poly_has_bin_op]; cbv [poly_mul].
  apply Spr1_inj. cbn.
  generalize dependent x. Admitted.

Global Instance poly_bin_op_is_comm_semigrp : IsCommSemigrp poly_mul.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_is_unl_l : IsUnlBinOpL null_op poly_mul.
Proof.
  intros x.
  cbv [bin_op poly_has_bin_op]; cbv [poly_mul]. Admitted.

Global Instance poly_bin_op_null_op_is_unl_r : IsUnlBinOpR null_op poly_mul.
Proof. intros x. Admitted.

Global Instance poly_bin_op_null_op_is_unl : IsUnlBinOpLR null_op poly_mul.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_is_mon : IsMon null_op poly_mul.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_is_comm_mon :
  IsCommMon poly_mul null_op.
Proof. split; typeclasses eauto. Defined.

End Context.

End Multiplicative.

Import OneSortedArithmeticNotations.
Import OneSortedArithmeticOperationNotations.

Section Context.

Context (A : Type) `{IsRing A} `{HasEqDec A} `{Countable A}.

Let poly := poly (A := A).

Global Instance poly_has_add : HasAdd poly := poly_add.
Global Instance poly_has_zero : HasZero poly := poly_zero.
Global Instance poly_has_neg : HasNeg poly := poly_neg.
Global Instance poly_has_mul : HasMul poly := poly_mul.
Global Instance poly_has_one : HasOne poly := poly_one.
Global Instance poly_has_act_l : HasActL A poly := poly_act_l.
Global Instance poly_has_act_r : HasActR A poly := poly_act_r.

Import Addition.Subclass Zero.Subclass Negation.Subclass
  Multiplication.Subclass One.Subclass.

Ltac conversions := typeclasses
  convert bin_op into (add (A := poly)) and
  null_op into (zero (A := poly)) and
  un_op into (neg (A := poly)) or
  convert bin_op into (mul (A := poly)) and
  null_op into (one (A := poly)) or
  convert bin_op into (add (A := A)) and
  null_op into (zero (A := A)) and
  un_op into (neg (A := A)) or
  convert bin_op into (mul (A := A)) and
  null_op into (one (A := A)).

Global Instance poly_add_mul_is_distr_l : IsDistrL mul add.
Proof. intros x y z. Admitted.

Global Instance poly_add_mul_is_distr_r : IsDistrR mul add.
Proof. intros x y z. Admitted.

Global Instance poly_add_mul_is_distr : IsDistrLR mul add.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_zero_mul_is_absorb_elem_l : IsAbsorbElemL zero mul.
Proof. intros x. Admitted.

Global Instance poly_zero_mul_is_absorb_elem_r : IsAbsorbElemR zero mul.
Proof. intros x. Admitted.

Global Instance poly_zero_mul_is_absorb_elem_l_r : IsAbsorbElemLR zero mul.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_add_zero_mul_one_is_semiring : IsSemiring add zero mul one.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_add_zero_mul_one_is_comm_semiring :
  IsCommSemiring add zero mul one.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_zero_neg_add_one_mul_is_ring :
  IsRing zero neg add one mul.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_mul_is_comm : IsComm mul.
Proof. intros x y. Admitted.

Global Instance poly_add_zero_neg_mul_one_is_comm_ring :
  IsCommRing add zero neg mul one.
Proof. split; typeclasses eauto. Defined.

(** We can now prove that the evaluation map is a homomorphism. *)

Lemma poly_eval_add : forall (p q : poly) (x : A),
  poly_eval (p + q) x = poly_eval p x + poly_eval q x.
Proof with conversions.
  intros p q x. etransitivity. cbv [add]. reflexivity.
  cbv [poly_has_add poly_add poly_eval]. cbn. Admitted.

Lemma poly_eval_zero : forall x : A,
  poly_eval 0 x = 0.
Proof with conversions.
  intros x. etransitivity. cbv [zero]. reflexivity.
  cbv [poly_has_zero poly_zero poly_eval]. cbn.
  rewrite map_imap_empty. reflexivity. Defined.

Lemma poly_eval_neg : forall (p : poly) (x : A),
  poly_eval (- p) x = - poly_eval p x.
Proof with conversions. Admitted.

Lemma poly_eval_mul : forall (p q : poly) (x : A),
  poly_eval (p * q) x = poly_eval p x * poly_eval q x.
Proof with conversions. Admitted.

Lemma poly_eval_one : forall x : A,
  poly_eval 1 x = 1.
Proof with conversions.
  intros x. etransitivity. cbv [one]. reflexivity.
  cbv [poly_has_one poly_one poly_eval]. cbn.
  decide (1 <> (0 : A)) as [F10 | F10].
  - rewrite map_imap_singleton.
    cbv [map_sum]. rewrite <- insert_empty. rewrite map_fold_insert_L.
    + cbn. rewrite map_fold_empty. rewrite unl_bin_op_r. cbv [poly_value_eval].
      rewrite unl_bin_op_l. reflexivity.
    + cbn. intros ? ? a b c **. rewrite assoc... rewrite (comm a b)...
      rewrite <- assoc... reflexivity.
    + rewrite lookup_empty. reflexivity.
  - apply dec_stable in F10. rewrite F10.
    rewrite map_imap_empty. reflexivity. Defined.

Import OneSortedGradedArithmeticNotations.

Definition poly_grd (i : N) : Type := A.

Global Instance poly_has_grd_mul : HasGrdMul poly_grd bin_op :=
  fun i j : N => mul.
Global Instance poly_has_grd_one : HasGrdOne poly_grd null_op :=
  one.

(** TODO Should never reference implicitly named variables like this. *)

Global Instance poly_is_grd_assoc :
  IsGrdAssoc (P := poly_grd) Additive.N_has_bin_op grd_mul.
Proof.
  esplit. intros i j k x y z. cbv [poly_grd]. rewrite rew_const.
  cbv [grd_bin_op grd_mul poly_has_grd_mul]. apply assoc. Defined.

Global Instance poly_is_grd_unl_l :
  IsGrdUnlL (P := poly_grd) Additive.N_has_bin_op
  Additive.N_has_null_op grd_mul grd_one.
Proof.
  esplit. intros i x. cbv [poly_grd]. rewrite rew_const.
  cbv [grd_bin_op grd_mul poly_has_grd_mul
    grd_null_op grd_one poly_has_grd_one]. apply unl_bin_op_l. Defined.

Global Instance poly_is_grd_unl_r :
  IsGrdUnlR (P := poly_grd) Additive.N_has_bin_op
  Additive.N_has_null_op grd_mul grd_one.
Proof.
  esplit. intros i x. cbv [poly_grd]. rewrite rew_const.
  cbv [grd_bin_op grd_mul poly_has_grd_mul
    grd_null_op grd_one poly_has_grd_one]. apply unl_bin_op_r. Defined.

Global Instance poly_is_grd_distr_l :
  IsGrdDistrL (P := poly_grd) bin_op (fun i : N => add) grd_mul.
Proof.
  intros i j x y z. cbv [grd_mul poly_has_grd_mul]. apply distr_l. Defined.

Global Instance poly_is_grd_distr_r :
  IsGrdDistrR (P := poly_grd) bin_op (fun i : N => add) grd_mul.
Proof.
  intros i j x y z. cbv [grd_mul poly_has_grd_mul]. apply distr_r. Defined.

Global Instance poly_is_grd_distr :
  IsGrdDistr (P := poly_grd) bin_op (fun i : N => add) grd_mul.
Proof. split; try typeclasses eauto. Defined.

Global Instance poly_is_grd_ring : IsGrdRing (P := fun i : N => A)
  bin_op null_op
  (fun i : N => add) (fun i : N => zero) (fun i : N => neg)
  (fun i j : N => mul) one.
Proof. split; try typeclasses eauto. Admitted.

Global Instance add_zero_neg_mul_one_is_alg :
  IsAlg (A := A) (B := poly)
  add zero neg mul one add zero neg mul act_l act_r.
Proof. split; try typeclasses eauto. Admitted.

Global Instance add_zero_neg_mul_one_is_assoc_alg :
  IsAssocAlg (A := A) (B := poly)
  add zero neg mul one add zero neg mul act_l act_r.
Proof. split; typeclasses eauto. Defined.

Global Instance add_zero_neg_mul_one_is_unl_assoc_alg :
  IsUnlAssocAlg (A := A) (B := poly)
  add zero neg mul one add zero neg mul one act_l act_r.
Proof. split; typeclasses eauto. Defined.

End Context.
