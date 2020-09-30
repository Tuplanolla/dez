(* bad *)
From Coq Require Import
  ZArith.ZArith.
From stdpp Require Import
  option fin_maps gmap pmap nmap.
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

Section Context.

Import OneSorted.ArithmeticNotations.

(** This is a weaker form of [EqDecision]. *)

Class HasZeroApart (A : Type) {has_zero : HasZero A} : Type :=
  zero_apart : forall x : A, Decision (x <> 0).

End Context.

Section Context.

Import OneSorted.ArithmeticNotations.

Context {A : Type} `{has_zero : HasZero A} `{eq_dec : EqDecision A}.

Global Instance A_has_zero_apart : HasZeroApart A :=
  fun x : A => decide (x <> 0).

End Context.

Section Context.

Import OneSorted.ArithmeticNotations.
Import OneSorted.ArithmeticOperationNotations.

Context {A : Type} `{is_ring : IsRing A} `{has_zero_apart : !HasZeroApart A}.

(** We cannot keep zero values in the map,
    because they would break definitional equality and
    needlessly increase space usage. *)

Definition NZ (a : A) : Prop := a <> 0.
Definition NZA : Type := {a : A | NZ a}.
Definition poly : Type := Nmap NZA.

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

Definition poly_eval (x : poly) (a : A) : A :=
  map_fold (fun (i : N) (b : NZA) (c : A) => c + `b * (a ^ i)%N) 0 x.

(** Addition of polynomials.

    The terms of the polynomials $x$, $y$ and $z$ in $z = x + y$
    are related by the parallel summation $z_n = x_n + y_n$ for all $n$.
    We need to prune zero terms after carrying out each addition,
    because it is possible that $z_n = 0$ for some $n$,
    even though $x_n \ne 0$ and $y_n \ne 0$;
    indeed, this happens whenever $y_n = - x_n$. *)

Program Definition poly_add (x y : poly) : poly :=
  union_with (fun a b : NZA => let c := `a + `b in
    if zero_apart c then Some (exist NZ c _) else None) x y.
Next Obligation. intros x y a b c F. cbv [NZ]. apply F. Defined.

(** Zero polynomial.

    The terms of the polynomial $x$ in $x = 0$
    are constrained by $x_n = 0$ for all $n$. *)

Definition poly_zero : poly :=
  empty.

(** Negation of polynomials.

    The terms of the polynomials $x$ and $y$ in $y = - x$
    are related by the pointwise negation $y_n = - x_n$ for all $n$. *)

Program Definition poly_neg (x : poly) : poly :=
  fmap (fun a : NZA => let b := - `a in exist NZ b _) x.
Next Obligation with conversions.
  intros x a b. cbv [NZ]. intros H.
  pose proof proj2_sig a as F; cbn in F; cbv [NZ] in F. apply F. apply inj...
  rewrite un_absorb...
  apply H. Defined.

(** Multiplication of polynomials.

    The terms of the polynomials $x$, $y$ and $z$ in $z = x \times y$
    are related by the discrete convolution
    $r_q = \sum_{n + p = q} x_n \times y_p$ for all $n$, $p$ and $q$.
    We need to prune the terms after carrying out each addition,
    because it is possible that $z_q = 0$ for some $q$,
    as was the case with $x + y$. *)

Program Definition poly_mul (x y : poly) : poly :=
  map_fold (fun (i : N) (a : NZA) (u : poly) =>
    map_fold (fun (j : N) (b : NZA) (v : poly) =>
      partial_alter (fun c : option NZA =>
        let d := `a * `b + from_option proj1_sig 0 c in
        if zero_apart d then Some (exist NZ d _) else None)
      (i + j) v) u y) empty x.
Next Obligation.
  intros x y i a u j b v c d F. cbv [NZ]. intros H. apply F. apply H. Defined.

(** Unit polynomial.

    The terms of the polynomial $x$ in $x = 1$
    are constrained by $x_0 = 1$ and $x_n = 0$ for all $n > 0$. *)

Program Definition poly_one : poly :=
  singletonM 0 (exist NZ 1 _).
(* TODO The ring must be nontrivial for this unit element to exist! *)
Next Obligation.
  cbv [NZ]. intros H. Admitted.

(** Left scalar multiplication of polynomials.

    The scalar $a$ and
    the terms of the polynomials $x$ and $y$ in $y = a \times x$
    are related by the pointwise multiplication
    $x_n = a \times x_n$ for all $n$. *)

Program Definition poly_l_act (a : A) (x : poly) : poly :=
  omap (fun b : NZA => let c := a * `b in
  if zero_apart c then Some (exist NZ c _) else None) x.
Next Obligation.
  intros a x b c F. cbv [NZ]. intros H. apply F. apply H. Defined.

(** Right scalar multiplication of polynomials.

    The scalar $a$ and
    the terms of the polynomials $x$ and $y$ in $y = x \times a$
    are related by the pointwise multiplication
    $x_n = x_n \times a$ for all $n$. *)

Program Definition poly_r_act (x : poly) (a : A) : poly :=
  omap (fun b : NZA => let c := `b * a in
  if zero_apart c then Some (exist NZ c _) else None) x.
Next Obligation.
  intros x a b c F. cbv [NZ]. intros H. apply F. apply H. Defined.

End Context.

Section Tests.

Local Open Scope Z_scope.

Obligation Tactic :=
  match goal with
  | |- NZ ?x => let H := fresh in
      hnf; destruct (zero_apart x) as [H | H]; auto
  end || auto.

(* 42 * x ^ 3 + 7 + 13 * x *)
Program Let p : poly := insert (N.add N.one N.two) (exist NZ 42 _)
  (insert N.zero (exist NZ 7 _) (insert N.one (exist NZ 13 _) empty)).

(* 3 * x ^ 4 + x + 5 *)
Program Let q : poly := insert (N.add N.two N.two) (exist NZ 3 _)
  (insert N.one (exist NZ 1 _) (insert N.zero (exist NZ 5 _) empty)).

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

End Tests.

Module Additive.

Import OneSorted.ArithmeticNotations.
Import OneSorted.AdditiveNotations.

Section Context.

Context {A : Type} `{is_ring : IsRing A} `{has_zero_apart : !HasZeroApart A}.

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

Global Instance poly_has_bin_op : HasBinOp poly := poly_add.
Global Instance poly_has_null_op : HasNullOp poly := poly_zero.
Global Instance poly_has_un_op : HasUnOp poly := poly_neg.

Global Instance poly_bin_op_is_mag : IsMag poly bin_op.
Proof. Defined.

Global Instance poly_bin_op_is_assoc : IsAssoc poly bin_op.
Proof with conversions.
  intros x y z. cbv [bin_op poly_has_bin_op poly_add].
  (** Peel the onion. *)
  cbv [union_with map_union_with].
  match goal with
  |- merge ?e x (merge ?e y z) = merge ?e (merge ?e x y) z => set (f := e)
  end.
  apply (merge_assoc' f).
  (** Cry. *)
  intros [a |] [b |] [c |].
  all: try reflexivity. 3:{
  cbv [f]. cbn.
  destruct (zero_apart (`b + `c)%ring) as [F | F].
  all: try reflexivity.
  }
  cbv [f]. cbn.
  destruct (zero_apart (`a + `b)%ring) as [Fab | Fab],
  (zero_apart (`b + `c)%ring) as [Fbc | Fbc].
  all: cbn. {
  destruct (zero_apart (`a + (`b + `c))%ring) as [Fabc | Fabc],
  (zero_apart ((`a + `b) + `c)%ring) as [Fabc' | Fabc'].
  f_equal. apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat.
  rewrite assoc. reflexivity.
  exfalso. apply Fabc'. rewrite <- assoc. apply Fabc.
  exfalso. apply Fabc. rewrite assoc. apply Fabc'.
  reflexivity.
  } {
  destruct (zero_apart ((`a + `b) + `c)%ring) as [Fabc' | Fabc'].
  shelve.
  exfalso. apply Fbc. intros H.
  rewrite <- assoc in Fabc'... rewrite H in Fabc'. rewrite r_unl in Fabc'.
  apply Fabc'. intros C. destruct a. hnf in n. apply n. apply C.
  } {
  destruct (zero_apart (`a + (`b + `c))%ring) as [Fabc | Fabc].
  shelve.
  exfalso. apply Fab. intros H.
  rewrite assoc in Fabc... rewrite H in Fabc. rewrite l_unl in Fabc.
  apply Fabc. intros C. destruct c. hnf in n. apply n. apply C.
  } {
  f_equal. destruct a, c.
  apply ProofIrrelevance.ProofIrrelevanceTheory.subset_eq_compat. cbn in *.
  enough (x0 + (`b + - `b) = (- `b + `b) + x1)%ring.
  rewrite l_inv, r_inv in H. rewrite l_unl, r_unl in H. apply H.
  rewrite assoc...
  enough (x0 + `b = 0)%ring.
  rewrite H. rewrite l_unl.
  enough (`b + x1 = 0)%ring.
  rewrite <- assoc...
  rewrite H0. rewrite r_unl. reflexivity.
  Admitted.

Global Instance poly_bin_op_is_sgrp : IsSgrp poly bin_op.
Proof. split; typeclasses eauto. Defined.

Local Open Scope ring_scope.

Global Instance poly_bin_op_is_comm : IsComm poly bin_op.
Proof.
  intros x y. cbv [bin_op poly_has_bin_op]. cbv [poly_add].
  (* TODO There is no instance matching [f |- Comm eq (union_with f)]. *)
  Admitted.

Global Instance poly_bin_op_is_comm_sgrp : IsCommSgrp poly bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_is_l_unl : IsLUnl poly bin_op null_op.
Proof.
  intros x.
  cbv [bin_op poly_has_bin_op]; cbv [poly_add].
  cbv [null_op poly_has_null_op]; cbv [poly_zero].
  (* TODO There is no instance. *)
  Admitted.

Global Instance poly_bin_op_null_op_is_r_unl : IsRUnl poly bin_op null_op.
Proof.
  intros x.
  cbv [bin_op poly_has_bin_op]; cbv [poly_add].
  cbv [null_op poly_has_null_op]; cbv [poly_zero].
  (* TODO There is no instance. *)
  Admitted.

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
  intros x.
  cbv [bin_op poly_has_bin_op]; cbv [poly_add].
  cbv [null_op poly_has_null_op]; cbv [poly_zero].
  cbv [un_op poly_has_un_op]; cbv [poly_neg]. Admitted.

Global Instance poly_bin_op_null_op_un_op_is_r_inv :
  IsRInv poly bin_op null_op un_op.
Proof.
  intros x.
  cbv [bin_op poly_has_bin_op]; cbv [poly_add].
  cbv [null_op poly_has_null_op]; cbv [poly_zero].
  cbv [un_op poly_has_un_op]; cbv [poly_neg]. Admitted.

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

Section Context.

Context {A : Type} `{is_ring : IsRing A} `{eq_dec : EqDecision A}.

Let poly := poly (A := A).

Global Instance poly_has_bin_op : HasBinOp poly := poly_mul.
Global Instance poly_has_null_op : HasNullOp poly := poly_one.

Global Instance poly_bin_op_is_mag : IsMag poly bin_op.
Proof. Defined.

Global Instance poly_bin_op_is_assoc : IsAssoc poly bin_op.
Proof. intros x y z. Admitted.

Global Instance poly_bin_op_is_sgrp : IsSgrp poly bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_is_comm : IsComm poly bin_op.
Proof.
  intros x y.
  cbv [bin_op poly_has_bin_op]; cbv [poly_mul]. Admitted.

Global Instance poly_bin_op_is_comm_sgrp : IsCommSgrp poly bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_is_l_unl : IsLUnl poly bin_op null_op.
Proof.
  intros x.
  cbv [bin_op poly_has_bin_op]; cbv [poly_mul].
  cbv [null_op poly_has_null_op]; cbv [poly_one].
  Admitted.

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

Global Instance poly_add_is_comm : IsComm poly add.
Proof with conversions.
  intros p q...
  cbv [add]; cbv [poly_has_add poly_add].
  Admitted.

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

Global Instance poly_is_grd_ring : IsGrdRing (fun i : N => A)
  (fun i : N => add) (fun i : N => zero) (fun i : N => neg)
  (fun i j : N => mul) one.
Proof. repeat split. Abort.

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
