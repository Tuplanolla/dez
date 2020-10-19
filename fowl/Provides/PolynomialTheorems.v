(* bad *)
From Coq Require Import
  ZArith.ZArith.
From stdpp Require Import
  option finite fin_maps gmap pmap nmap.
From Maniunfold.Has Require Export
  OneSorted.Enumeration OneSorted.Cardinality TwoSorted.Isomorphism.
From Maniunfold.Is Require Export
  OneSorted.Finite TwoSorted.Isomorphism
  OneSorted.Ring TwoSorted.UnitalAssociativeAlgebra TwoSorted.Graded.Algebra.
From Maniunfold.Is Require Export
  OneSorted.AbelianGroup OneSorted.CommutativeSemigroup
  OneSorted.CommutativeMonoid OneSorted.CommutativeSemiring
  OneSorted.CommutativeRing.
From Maniunfold.Offers Require Export
  TwoSorted.IsomorphismMappings
  OneSorted.PositiveOperations OneSorted.NaturalOperations
  OneSorted.IntegerOperations.
From Maniunfold.Provides Require Export
  NTheorems ZTheorems.
From Maniunfold.ShouldHave Require
  OneSorted.AdditiveNotations OneSorted.MultiplicativeNotations.
From Maniunfold.ShouldHave Require
  OneSorted.ArithmeticNotations.
From Maniunfold.ShouldOffer Require
  OneSorted.ArithmeticOperationNotations.

Section more_merge.

Context `{FinMap K M}.

Context {A B C} (f : option A → option B → option C) `{!DiagNone f}.

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

(** Not a pullback of a finite map along a key altering function. *)

Definition map_pullback {K L A MK ML : Type}
  `{FinMapToList K A MK} `{Empty ML} `{PartialAlter L A ML}
  (p : K -> L) (x : MK) : ML :=
  map_fold (fun (i : K) (x : A) (y : ML) =>
    partial_alter (fun y : option A => Some x) (p i) y) empty x.

Definition map_free_pullback {K L A MK ML : Type}
  `{FinMapToList K A MK} `{Empty ML} `{PartialAlter L (list A) ML}
  (p : K -> L) (x : MK) : ML :=
  map_fold (fun (i : K) (x : A) (y : ML) =>
    partial_alter (fun y : option (list A) =>
      Some (x :: default [] y)) (p i) y) empty x.

(** The order should be unspecified. *)

Lemma map_pullbacks {K L A MK ML : Type}
  `{FinMapToList K A MK} `{Empty ML}
  `{PartialAlter L A ML} `{PartialAlter L (list A) ML}
  `{FMap (const MK)} `{FMap (const ML)}
  (p : K -> L) (x : MK) :
  Some (A := A) <$> map_pullback p x = hd_error <$> map_free_pullback p x.
Proof. Admitted.

Lemma map_pullback_fmap {K L A B MK ML : Type}
  `{FinMapToList K A MK} `{Empty ML} `{PartialAlter L A ML}
  `{FMap (const MK)} `{FMap (const ML)}
  (p : K -> L) (f : A -> B) (x : MK) :
  f <$> map_pullback p x = map_pullback p (f <$> x).
Proof. cbv [map_pullback]. Admitted.

Lemma map_free_pullback_fmap {K L A B MK ML : Type} {P : L -> A -> Prop}
  `{FinMapToList K A MK} `{Empty ML} `{PartialAlter L (list A) ML}
  `{Lookup K A MK} `{Lookup L (list A) ML}
  `{FMap (const MK)} `{FMap (const ML)}
  (p : K -> L) (f : A -> B) (x : MK) :
  fmap f <$> map_free_pullback p x = map_free_pullback p (f <$> x).
Proof. Admitted.

Lemma map_Forall_pullback {K L A MK ML : Type} {P : L -> A -> Prop}
  `{FinMapToList K A MK} `{Empty ML} `{PartialAlter L (list A) ML}
  `{Lookup K A MK} `{Lookup L (list A) ML}
  (p : K -> L) (x : MK) :
  map_Forall (fun (i : K) (a : A) => P (p i) a) x <->
  map_Forall (fun (i : L) (a : list A) => Forall (P i) a)
  (map_free_pullback (MK := MK) (ML := ML) p x).
Proof. Admitted.

Lemma map_Forall_pullback_const {K L A MK ML : Type} {P : A -> Prop}
  `{FinMapToList K A MK} `{Empty ML} `{PartialAlter L (list A) ML}
  `{Lookup K A MK} `{Lookup L (list A) ML}
  (p : K -> L) (x : MK) :
  map_Forall (const P) x <->
  map_Forall (const (Forall P)) (map_free_pullback (MK := MK) (ML := ML) p x).
Proof. exact (map_Forall_pullback p x). Defined.

(** Free product of two finite maps along their keys. *)

Definition map_free_prod {KA KB A B MA MB MAB : Type}
  `{FinMapToList KA A MA} `{FinMapToList KB B MB}
  `{Empty MAB} `{Insert (KA * KB) (A * B) MAB}
  (x : MA) (y : MB) : MAB :=
  map_fold (fun (i : KA) (a : A) (z : MAB) =>
    map_fold (fun (j : KB) (b : B) (z : MAB) =>
      insert (i, j) (a, b) z) z y) empty x.

Definition map_proj1 {KA KB A B MA MB MAB : Type}
  `{FinMapToList (KA * KB) A MAB} `{Empty MA}
  `{FMap (const MA)} `{PartialAlter KA A MA}
  (x : MAB) : MA :=
  @fst A B <$> map_pullback fst x.

Definition map_proj1' {KA KB A B MA MB MAB : Type}
  `{FinMapToList (KA * KB) A MAB} `{Empty MA}
  `{FMap (const MAB)} `{PartialAlter KA A MA}
  (x : MAB) : MA :=
  map_pullback fst (@fst A B <$> x).

Lemma map_free_prod_1 {KA KB A B MA MB MAB : Type}
  `{FinMapToList KA A MA} `{FinMapToList KB B MB}
  `{FinMapToList (KA * KB) A MAB}
  `{Empty MA} `{Empty MAB} `{Insert (KA * KB) (A * B) MAB}
  `{FMap (const MA)} `{PartialAlter KA A MA}
  (x : MA) (y : MB) :
  map_proj1 (B := B) (MB := MB) (map_free_prod x y) = x.
Proof. Admitted.

(** If we wish to state that [map_free_prod] is associative,
    we need to transport one side of the equation via [assoc] on [prod].
    However, inhabiting this instance of [assoc] requires univalence.
    We could also express the property pointwise,
    but that still requires pointwise transport with [fmap].
    More generally, [map_free_prod] is free,
    so it commutes with all the obvious things. *)

Lemma map_free_prod_fmap {KA KB A B MA MB MAB A' B' MA' MB' MAB' : Type}
  `{FinMapToList KA A MA} `{FinMapToList KB B MB}
  `{Empty MAB} `{Insert (KA * KB) (A * B) MAB}
  `{FMap (const MA)} `{FMap (const MB)} `{FMap (const MAB)}
  (f : A -> A') (g : B -> B') (x : MA) (y : MB) :
  prod_map f g <$> map_free_prod x y = map_free_prod (f <$> x) (g <$> y).
Proof. Admitted.

Check let map_pullback_prod_flip {KA KB KC A B C MA MB : Type}
  (p : KA -> KB -> KC) (f : A -> B -> C) (x : MA) (y : MB) :=
  map_free_pullback (K := KA * KB) (L := KC) (A := C)
  (uncurry p) (uncurry f <$> map_free_prod x y) =
  map_free_pullback (K := KB * KA) (L := KC) (A := C)
  (uncurry (flip p)) (uncurry (flip f) <$> map_free_prod y x) in
  map_pullback_prod_flip.

Lemma filter_fmap {A B : Type} {M : Type -> Type}
  `{FMap M} `{Filter A (M A)} `{Filter B (M B)}
  (P : A -> Prop) `{forall x : A, Decision (P x)}
  (f : B -> A) `{forall x : B, Decision (compose P f x)} (xs : M B) :
  filter P (f <$> xs) = f <$> filter (compose P f) xs.
Proof. Abort.

(** A finite map is equivalent to a function with finite support.
    Almost, at least. We also need an upper bound for the largest key. *)

Definition almost_maplike {K A : Type} `{HasZero A} : Type :=
  {f : K -> A | exists `(Finite J), forall project : J -> K,
    forall i : K, ~ (exists j : J, project j = i) -> f i = zero}.

Definition actually_maplike {K A : Type} `{Finite K} `{HasZero A} : Type :=
  K -> A.

Section Context.

Import OneSorted.ArithmeticNotations.

Definition map_sum {K A M : Type}
  `{FinMapToList K A M} `{HasAdd A} `{HasZero A}
  (m : M) : A := map_fold (const add) 0 m.

Definition map_product {K A M : Type}
  `{FinMapToList K A M} `{HasMul A} `{HasOne A}
  (m : M) : A := map_fold (const mul) 1 m.

Definition list_sum {A : Type}
  `{HasAdd A} `{HasZero A}
  (l : list A) : A := foldr add 0 l.

Definition list_product {A : Type}
  `{HasMul A} `{HasOne A}
  (l : list A) : A := foldr mul 1 l.

End Context.

Section Context.

Import OneSorted.ArithmeticNotations.
Import OneSorted.ArithmeticOperationNotations.

Context {A : Type} `{is_ring : IsRing A} `{eq_dec : EqDecision A}.

(** We cannot keep zero values in the map,
    because they would break definitional equality and
    needlessly increase space usage. *)

Definition poly_value_wf (n : N) (a : A) : Prop := bool_decide (a <> 0).
Definition poly_wf (m : gmap N A) : Prop :=
  bool_decide (map_Forall poly_value_wf m).
Definition poly : Type := {m : gmap N A | poly_wf m}.

Lemma poly_lookup_wf : forall (x : poly) (i : N),
  `x !! i <> Some 0.
Proof.
  intros [x Wp] i. intros H.
  pose proof Wp as Wp'. apply bool_decide_unpack in Wp'.
  pose proof map_Forall_lookup_1 poly_value_wf x i 0 Wp' H as Wc.
  apply bool_decide_unpack in Wc. apply Wc. reflexivity. Defined.

Ltac stabilize :=
  repeat match goal with
  | H : ~ ?a <> ?b |- _ => apply dec_stable in H
  end.

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
  exist poly_wf (union_with (fun a b : A => let c := a + b in
    if decide (c <> 0) then Some c else None) (`x) (`y)) _.
Next Obligation.
  intros x y. apply bool_decide_pack.
  intros i a H. apply bool_decide_pack. intros Ha. subst a.
  apply lookup_union_with_Some in H. cbn in H.
  destruct H as [[Hx Hy] | [[Hx Hy] | [a [b [Hx [Hy Hxy]]]]]].
  - apply (poly_lookup_wf x i Hx).
  - apply (poly_lookup_wf y i Hy).
  - cbv zeta in Hxy. destruct (decide (a + b <> 0)) as [Fab | Fab]; stabilize.
    + inversion Hxy as [Hab]. apply Fab. apply Hab.
    + inversion Hxy. Defined.

(** Zero polynomial.

    The terms of the polynomial $x$ in $x = 0$
    are constrained by $x_n = 0$ for all $n$. *)

Program Definition poly_zero : poly := exist poly_wf empty _.
Next Obligation.
  apply bool_decide_pack.
  intros i a H. apply bool_decide_pack. intros Ha. subst a.
  apply lookup_empty_Some in H.
  destruct H. Defined.

(** Negation of polynomials.

    The terms of the polynomials $x$ and $y$ in $y = - x$
    are related by the pointwise negation $y_n = - x_n$ for all $n$. *)

Program Definition poly_neg (x : poly) : poly :=
  exist poly_wf (neg <$> `x) _.
Next Obligation with conversions.
  intros x. apply bool_decide_pack.
  intros i a H. apply bool_decide_pack. intros Ha. subst a.
  rewrite lookup_fmap in H.
  pose proof fmap_Some_1 _ _ _ H as H'.
  destruct H' as [a [Hx Hy]].
  rewrite <- un_absorb in Hy... apply inj in Hy. subst a.
  apply (poly_lookup_wf x i Hx). Defined.

(** Multiplication of polynomials.

    The terms of the polynomials $x$, $y$ and $z$ in $z = x \times y$
    are related by the discrete convolution
    $r_q = \sum_{n + p = q} x_n \times y_p$ for all $n$, $p$ and $q$.
    We need to prune the terms after carrying out each addition,
    because it is possible that $z_q = 0$ for some $q$,
    as was the case with $x + y$. *)

Program Definition poly_mul (x y : poly) : poly :=
  exist poly_wf (filter (uncurry poly_value_wf)
    (list_sum <$> map_free_pullback (uncurry add (A := N))
      (uncurry mul <$> map_free_prod (`x) (`y)))) _.
Next Obligation.
  intros x y. apply bool_decide_pack.
  intros i a H. apply bool_decide_pack. intros Ha. subst a.
  apply map_filter_lookup_Some in H.
  destruct H as [H Wc].
  apply bool_decide_unpack in Wc. apply Wc. reflexivity. Defined.

(** Unit polynomial.

    The terms of the polynomial $x$ in $x = 1$
    are constrained by $x_0 = 1$ and $x_n = 0$ for all $n > 0$. *)

Program Definition poly_one : poly :=
  exist poly_wf (if decide (1 <> 0) then singletonM 0 1 else empty) _.
Next Obligation.
  apply bool_decide_pack.
  intros i a H. apply bool_decide_pack. intros Ha. subst a.
  destruct (decide (1 <> 0)) as [F10 | F10]; stabilize.
  - rewrite lookup_singleton_ne in H.
    + inversion H.
    + intros Hi. subst i. rewrite lookup_singleton in H. inversion H as [H10].
      apply F10. apply H10.
  - rewrite lookup_empty in H. inversion H. Defined.

(** We could use the zero-product property to speed up computations here,
    but not fully, because our ring may not be a domain. *)

(** Left scalar multiplication of polynomials.

    The scalar $a$ and
    the terms of the polynomials $x$ and $y$ in $y = a \times x$
    are related by the pointwise multiplication
    $x_n = a \times x_n$ for all $n$. *)

Program Definition poly_l_act (a : A) (x : poly) : poly :=
  exist poly_wf (filter (uncurry poly_value_wf) (mul a <$> `x)) _.
Next Obligation with conversions.
  intros a x. apply bool_decide_pack.
  intros i b H. apply bool_decide_pack. intros Hb. subst b.
  apply map_filter_lookup_Some in H.
  destruct H as [H Wc].
  apply bool_decide_unpack in Wc. apply Wc. reflexivity. Defined.

(** Right scalar multiplication of polynomials.

    The scalar $a$ and
    the terms of the polynomials $x$ and $y$ in $y = x \times a$
    are related by the pointwise multiplication
    $x_n = x_n \times a$ for all $n$. *)

Program Definition poly_r_act (x : poly) (a : A) : poly :=
  exist poly_wf (filter (uncurry poly_value_wf) (flip mul a <$> `x)) _.
Next Obligation with conversions.
  intros a x. apply bool_decide_pack.
  intros i b H. apply bool_decide_pack. intros Hb. subst b.
  apply map_filter_lookup_Some in H.
  destruct H as [H Wc].
  apply bool_decide_unpack in Wc. apply Wc. reflexivity. Defined.

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

Import OneSorted.AdditiveNotations.
Import OneSorted.ArithmeticNotations.

Section Context.

Context {A : Type} `{is_ring : IsRing A} `{eq_dec : EqDecision A}.

(** Performing this specialization by hand aids type inference. *)

Let poly := poly (A := A).

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

Global Instance poly_bin_op_is_mag : IsMag poly bin_op.
Proof. Defined.

Global Instance poly_bin_op_is_assoc : IsAssoc poly bin_op.
Proof with conversions.
  intros x y z.
  cbv [bin_op poly_has_bin_op poly_add]. cbn.
  apply sig_eq_pi; [typeclasses eauto |]. cbn.
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
  destruct (decide (a + b <> 0)) as [Fab | Fab],
  (decide (b + c <> 0)) as [Fbc | Fbc]; stabilize; cbn.
  - destruct (decide (a + (b + c) <> 0)) as [Fa_bc | Fa_bc],
    (decide ((a + b) + c <> 0)) as [Fab_c | Fab_c]; stabilize; cbn.
    + f_equal. rewrite assoc... reflexivity.
    + exfalso. apply Fa_bc. rewrite assoc... apply Fab_c.
    + exfalso. apply Fab_c. rewrite <- assoc... apply Fa_bc.
    + reflexivity.
  - destruct (decide ((a + b) + c <> 0)) as [Fab_c | Fab_c];
    stabilize; cbn.
    + f_equal. rewrite <- assoc... rewrite Fbc. rewrite r_unl. reflexivity.
    + exfalso. rewrite <- assoc in Fab_c...
      rewrite Fbc in Fab_c. rewrite r_unl in Fab_c.
      subst a. apply (poly_lookup_wf x i). apply Dx.
  - destruct (decide (a + (b + c) <> 0)) as [Fa_bc | Fa_bc];
    stabilize; cbn.
    + f_equal. rewrite assoc... rewrite Fab. rewrite l_unl. reflexivity.
    + exfalso. rewrite assoc in Fa_bc...
      rewrite Fab in Fa_bc. rewrite l_unl in Fa_bc.
      subst c. apply (poly_lookup_wf z i). apply Dz.
  - f_equal. assert (Ha : a = a + (b + - b)).
    { rewrite r_inv. rewrite r_unl. reflexivity. }
    assert (Hc : c = (- b + b) + c).
    { rewrite l_inv. rewrite l_unl. reflexivity. }
    rewrite Ha. rewrite assoc...
    rewrite Fab. rewrite l_unl.
    rewrite Hc. rewrite <- assoc...
    rewrite Fbc. rewrite r_unl. reflexivity. Defined.

Global Instance poly_bin_op_is_sgrp : IsSgrp poly bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_is_comm : IsComm poly bin_op.
Proof with conversions.
  intros x y. cbv [bin_op poly_has_bin_op poly_add].
  cbv [union_with map_union_with].
  apply sig_eq_pi; [typeclasses eauto |]. cbn.
  match goal with
  |- merge ?e _ _ = merge ?e _ _ => set (f := e)
  end.
  apply (merge_comm f).
  intros i.
  destruct (`x !! i) as [a |] eqn : Dx,
  (`y !! i) as [b |] eqn : Dy; try reflexivity.
  cbv [f].
  cbv [union_with option_union_with].
  destruct (decide (a + b <> 0)) as [Fab | Fab],
  (decide (b + a <> 0)) as [Fba | Fba]; stabilize; cbn.
  - f_equal. rewrite comm... reflexivity.
  - exfalso. apply Fab. rewrite comm... apply Fba.
  - exfalso. apply Fba. rewrite comm... apply Fab.
  - reflexivity. Defined.

Global Instance poly_bin_op_is_comm_sgrp : IsCommSgrp poly bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_is_l_unl : IsLUnl poly bin_op null_op.
Proof.
  intros x. cbv [bin_op poly_has_bin_op poly_add
  null_op poly_has_null_op poly_zero].
  cbv [union_with map_union_with].
  Fail apply (left_id empty (merge (option_union_with _))). Admitted.

Global Instance poly_bin_op_null_op_is_r_unl : IsRUnl poly bin_op null_op.
Proof.
  intros x. cbv [bin_op poly_has_bin_op poly_add
  null_op poly_has_null_op poly_zero].
  cbv [union_with map_union_with].
  Fail apply (right_id empty (merge (option_union_with _))). Admitted.

Global Instance poly_bin_op_null_op_is_unl : IsUnl poly bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_is_mon : IsMon poly bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_is_comm_mon :
  IsCommMon poly bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_un_op_is_l_inv :
  IsLInv poly bin_op null_op un_op.
Proof.
  intros x. cbv [bin_op poly_has_bin_op poly_add
  null_op poly_has_null_op poly_zero
  un_op poly_has_un_op poly_neg].
  cbv [union_with map_union_with]. Admitted.

Global Instance poly_bin_op_null_op_un_op_is_r_inv :
  IsRInv poly bin_op null_op un_op.
Proof.
  intros x. cbv [bin_op poly_has_bin_op poly_add
  null_op poly_has_null_op poly_zero
  un_op poly_has_un_op poly_neg].
  cbv [union_with map_union_with]. Admitted.

Global Instance poly_bin_op_null_op_un_op_is_inv :
  IsInv poly bin_op null_op un_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_un_op_is_grp :
  IsGrp poly bin_op null_op un_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_un_op_is_ab_grp :
  IsAbGrp poly bin_op null_op un_op.
Proof. split; typeclasses eauto. Defined.

End Context.

End Additive.

Module Multiplicative.

Import OneSorted.MultiplicativeNotations.
Import OneSorted.ArithmeticNotations.

Section Context.

Context {A : Type} `{is_ring : IsRing A} `{eq_dec : EqDecision A}.

Let poly := poly (A := A).

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

Global Instance poly_bin_op_is_mag : IsMag poly bin_op.
Proof. Defined.

Global Instance poly_bin_op_is_assoc : IsAssoc poly bin_op.
Proof with conversions.
  intros x y z.
  cbv [bin_op poly_has_bin_op poly_mul]. cbn.
  apply sig_eq_pi; [typeclasses eauto |]. cbn.
  match goal with
  |- filter ?e _ = filter ?e _ => set (P := e)
  end.
  set (f (x y : gmap N A) :=
    filter P
    (summation <$>
      map_free_pullback (K := N * N) (L := N) (uncurry add)
        (uncurry mul <$>
          map_free_prod x y)) : gmap N A).
  enough (f (`x) (f (`y) (`z)) = f (f (`x) (`y)) (`z)) by assumption.
  destruct x as [m Wm]. cbn.
  generalize dependent m.
  apply (map_ind (fun m : gmap N A => poly_wf m → f m (f (`y) (`z)) = f (f m (`y)) (`z))).
  - intros W. cbv [f]. reflexivity.
  - intros i x m H IH W. cbv [f]. Admitted.

Global Instance poly_bin_op_is_sgrp : IsSgrp poly bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_is_comm : IsComm poly bin_op.
Proof.
  intros x y.
  cbv [bin_op poly_has_bin_op]; cbv [poly_mul].
  apply sig_eq_pi; [typeclasses eauto |]. cbn.
  generalize dependent x. Admitted.

Global Instance poly_bin_op_is_comm_sgrp : IsCommSgrp poly bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_is_l_unl : IsLUnl poly bin_op null_op.
Proof.
  intros x.
  cbv [bin_op poly_has_bin_op]; cbv [poly_mul]. Admitted.

Global Instance poly_bin_op_null_op_is_r_unl : IsRUnl poly bin_op null_op.
Proof. intros x. Admitted.

Global Instance poly_bin_op_null_op_is_unl : IsUnl poly bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_is_mon : IsMon poly bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_is_comm_mon :
  IsCommMon poly bin_op null_op.
Proof. split; typeclasses eauto. Defined.

End Context.

End Multiplicative.

Import OneSorted.ArithmeticNotations.
Import OneSorted.ArithmeticOperationNotations.

Import OneSorted.Graded.ArithmeticNotations.

Section Context.

Context {A : Type} `{is_ring : IsRing A} `{eq_dec : EqDecision A}.

Let poly := poly (A := A).

Global Instance poly_has_add : HasAdd poly := poly_add.
Global Instance poly_has_zero : HasZero poly := poly_zero.
Global Instance poly_has_neg : HasNeg poly := poly_neg.
Global Instance poly_has_mul : HasMul poly := poly_mul.
Global Instance poly_has_one : HasOne poly := poly_one.
Global Instance poly_has_l_act : HasLAct A poly := poly_l_act.
Global Instance poly_has_r_act : HasRAct A poly := poly_r_act.

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

Global Instance poly_add_mul_is_l_distr : IsLDistr poly add mul.
Proof. intros x y z. Admitted.

Global Instance poly_add_mul_is_r_distr : IsRDistr poly add mul.
Proof. intros x y z. Admitted.

Global Instance poly_add_mul_is_distr : IsDistr poly add mul.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_zero_mul_is_l_absorb : IsLAbsorb poly zero mul.
Proof. intros x. Admitted.

Global Instance poly_zero_mul_is_r_absorb : IsRAbsorb poly zero mul.
Proof. intros x. Admitted.

Global Instance poly_zero_mul_is_absorb : IsAbsorb poly zero mul.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_add_zero_mul_one_is_sring : IsSring poly add zero mul one.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_add_zero_mul_one_is_comm_sring :
  IsCommSring poly add zero mul one.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_add_zero_neg_mul_one_is_ring :
  IsRing poly add zero neg mul one.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_mul_is_comm : IsComm poly mul.
Proof. intros x y. Admitted.

Global Instance poly_add_zero_neg_mul_one_is_comm_ring :
  IsCommRing poly add zero neg mul one.
Proof. split; typeclasses eauto. Defined.

Definition poly_grd (i : N) : Type := A.

Global Instance poly_has_grd_mul : HasGrdMul poly_grd := fun i j : N => mul.
Global Instance poly_has_grd_one : HasGrdOne poly_grd := one.

Global Instance poly_is_grd_assoc :
  IsGrdAssoc poly_grd (A_has_bin_op := Additive.N_has_bin_op) grd_mul.
Proof.
  esplit. intros i j k x y z. cbv [poly_grd]. rewrite rew_const.
  cbv [grd_bin_op grd_mul poly_has_grd_mul]. apply assoc. Defined.

Global Instance poly_is_grd_l_unl :
  IsGrdLUnl poly_grd (A_has_bin_op := Additive.N_has_bin_op)
  (A_has_null_op := Additive.N_has_null_op) grd_mul grd_one.
Proof.
  esplit. intros i x. cbv [poly_grd]. rewrite rew_const.
  cbv [grd_bin_op grd_mul poly_has_grd_mul
    grd_null_op grd_one poly_has_grd_one]. apply l_unl. Defined.

Global Instance poly_is_grd_r_unl :
  IsGrdRUnl poly_grd (A_has_bin_op := Additive.N_has_bin_op)
  (A_has_null_op := Additive.N_has_null_op) grd_mul grd_one.
Proof.
  esplit. intros i x. cbv [poly_grd]. rewrite rew_const.
  cbv [grd_bin_op grd_mul poly_has_grd_mul
    grd_null_op grd_one poly_has_grd_one]. apply r_unl. Defined.

Global Instance poly_is_grd_l_distr :
  IsGrdLDistr poly_grd (fun i : N => add) grd_mul.
Proof.
  intros i j x y z. cbv [grd_mul poly_has_grd_mul]. apply l_distr. Defined.

Global Instance poly_is_grd_r_distr :
  IsGrdRDistr poly_grd (fun i : N => add) grd_mul.
Proof.
  intros i j x y z. cbv [grd_mul poly_has_grd_mul]. apply r_distr. Defined.

Global Instance poly_is_grd_distr :
  IsGrdDistr poly_grd (fun i : N => add) grd_mul.
Proof. split; try typeclasses eauto. Defined.

Global Instance poly_is_grd_ring : IsGrdRing (fun i : N => A)
  (fun i : N => add) (fun i : N => zero) (fun i : N => neg)
  (fun i j : N => mul) one.
Proof. split; try typeclasses eauto. Admitted.

Global Instance add_zero_neg_mul_one_is_alg :
  IsAlg A poly add zero neg mul one add zero neg mul l_act r_act.
Proof. split; try typeclasses eauto. Admitted.

Global Instance add_zero_neg_mul_one_is_assoc_alg :
  IsAssocAlg A poly add zero neg mul one add zero neg mul l_act r_act.
Proof. split; typeclasses eauto. Defined.

Global Instance add_zero_neg_mul_one_is_unl_assoc_alg :
  IsUnlAssocAlg A poly add zero neg mul one add zero neg mul one l_act r_act.
Proof. split; typeclasses eauto. Defined.

End Context.
