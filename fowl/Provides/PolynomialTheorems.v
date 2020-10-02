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
Import OneSorted.ArithmeticOperationNotations.

Context {A : Type} `{is_ring : IsRing A} `{eq_dec : EqDecision A}.

(** We cannot keep zero values in the map,
    because they would break definitional equality and
    needlessly increase space usage. *)

Definition NZ (a : A) : Prop := bool_decide (a <> 0).
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
    if decide (c <> 0) then Some (exist NZ c _) else None) x y.
Next Obligation.
  intros x y a b c F. cbv [NZ]. apply bool_decide_pack. apply F. Defined.

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
  intros x a b. cbv [NZ]. apply bool_decide_pack. intros H.
  pose proof proj2_sig a as F; cbn in F; cbv [NZ] in F.
  apply bool_decide_unpack in F. apply F. apply inj...
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
        if decide (d <> 0) then Some (exist NZ d _) else None)
      (i + j) v) u y) empty x.
Next Obligation.
  intros x y i a u j b v c d F. cbv [NZ]. apply bool_decide_pack.
  intros H. apply F. apply H. Defined.

(** Unit polynomial.

    The terms of the polynomial $x$ in $x = 1$
    are constrained by $x_0 = 1$ and $x_n = 0$ for all $n > 0$. *)

Program Definition poly_one : poly :=
  if decide (1 <> 0) then singletonM 0 (exist NZ 1 _) else empty.
Next Obligation.
  intros H. cbv [NZ]. apply bool_decide_pack. apply H. Defined.

(** Left scalar multiplication of polynomials.

    The scalar $a$ and
    the terms of the polynomials $x$ and $y$ in $y = a \times x$
    are related by the pointwise multiplication
    $x_n = a \times x_n$ for all $n$. *)

Program Definition poly_l_act (a : A) (x : poly) : poly :=
  omap (fun b : NZA => let c := a * `b in
  if decide (c <> 0) then Some (exist NZ c _) else None) x.
Next Obligation.
  intros a x b c F. cbv [NZ]. apply bool_decide_pack.
  intros H. apply F. apply H. Defined.

(** Right scalar multiplication of polynomials.

    The scalar $a$ and
    the terms of the polynomials $x$ and $y$ in $y = x \times a$
    are related by the pointwise multiplication
    $x_n = x_n \times a$ for all $n$. *)

Program Definition poly_r_act (x : poly) (a : A) : poly :=
  omap (fun b : NZA => let c := `b * a in
  if decide (c <> 0) then Some (exist NZ c _) else None) x.
Next Obligation.
  intros x a b c F. cbv [NZ]. apply bool_decide_pack.
  intros H. apply F. apply H. Defined.

End Context.

Section Tests.

Local Open Scope Z_scope.

Obligation Tactic :=
  match goal with
  | |- NZ ?x => let H := fresh in
      hnf; destruct (decide (x <> 0)) as [H | H]; auto
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

Global Instance poly_has_bin_op : HasBinOp poly := poly_add.
Global Instance poly_has_null_op : HasNullOp poly := poly_zero.
Global Instance poly_has_un_op : HasUnOp poly := poly_neg.

Global Instance poly_bin_op_is_mag : IsMag poly bin_op.
Proof. Defined.

Global Instance poly_bin_op_is_assoc : IsAssoc poly bin_op.
Proof with conversions.
  intros x y z.
  cbv [bin_op poly_has_bin_op poly_add].
  (** Peel the onion. *)
  cbv [union_with map_union_with].
  replace option_union_with with (union_with (M := option NZA))
  by reflexivity.
  match goal with
  |- merge ?e ?x (merge ?e ?y ?z) = merge ?e (merge ?e ?x ?y) ?z =>
      set (f := e)
  end.
  apply (merge_assoc' f).
  clear poly x y z.
  intros [a |] [b |] [c |].
  all: try reflexivity.
  all: cycle 1.
  cbv [f]. repeat rewrite union_with_right_id. reflexivity.
  cbv [f]. repeat rewrite union_with_left_id. reflexivity.
  (** Cry. *)
  cbv [f]. cbv [union_with option_union_with].
  destruct (decide (`a + `b <> 0)%ring) as [Fab | Fab],
  (decide (`b + `c <> 0)%ring) as [Fbc | Fbc].
  cbn.
  destruct (decide (`a + (`b + `c) <> 0)%ring) as [Fa_bc | Fa_bc],
  (decide ((`a + `b) + `c <> 0)%ring) as [Fab_c | Fab_c].
  f_equal. apply sig_eq_pi. intros x. apply Is_true_pi.
  cbn. rewrite assoc... reflexivity.
  exfalso. apply Fab_c. intros Hab_c. rewrite <- assoc in Hab_c...
  rewrite Hab_c in Fa_bc. apply Fa_bc. reflexivity.
  exfalso. apply Fa_bc. intros Ha_bc. rewrite assoc in Ha_bc...
  rewrite Ha_bc in Fab_c. apply Fab_c. reflexivity.
  reflexivity.
  cbn.
  destruct (decide ((`a + `b) + `c <> 0)%ring) as [Fab_c | Fab_c].
  f_equal. apply sig_eq_pi. intros x. apply Is_true_pi.
  cbn. apply dec_stable in Fbc. rewrite <- assoc...
  rewrite Fbc. rewrite r_unl. reflexivity.
  exfalso. apply Fab_c. apply dec_stable in Fbc. rewrite <- assoc...
  rewrite Fbc. rewrite r_unl. pose proof proj2_sig a as H. hnf in H.
  rewrite <- decide_bool_decide in H.
  destruct (decide (`a <> 0)%ring) as [Fa | Fa].
  apply Fa. inversion H.
  cbn.
  destruct (decide (`a + (`b + `c) <> 0)%ring) as [Fa_bc | Fa_bc].
  f_equal. apply sig_eq_pi. intros x. apply Is_true_pi.
  cbn. apply dec_stable in Fab. rewrite assoc...
  rewrite Fab. rewrite l_unl. reflexivity.
  exfalso. apply Fab. intros Hab. apply Fa_bc. rewrite assoc...
  rewrite Hab. rewrite l_unl. pose proof proj2_sig c as H. hnf in H.
  rewrite <- decide_bool_decide in H.
  destruct (decide (`c <> 0)%ring) as [Fc | Fc].
  apply Fc. inversion H.
  apply dec_stable in Fab. apply dec_stable in Fbc.
  f_equal. apply sig_eq_pi. intros x. apply Is_true_pi.
  replace (`a) with (`a + (`b + - `b))%ring. rewrite assoc...
  rewrite Fab. rewrite l_unl.
  replace (`c) with ((- `b + `b) + `c)%ring. rewrite <- assoc...
  rewrite Fbc. rewrite r_unl. reflexivity.
  rewrite l_inv. rewrite l_unl. reflexivity.
  rewrite r_inv. rewrite r_unl. reflexivity. Defined.

Global Instance poly_bin_op_is_sgrp : IsSgrp poly bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_is_comm : IsComm poly bin_op.
Proof with conversions.
  intros x y. cbv [bin_op poly_has_bin_op poly_add].
  cbv [union_with map_union_with].
  replace option_union_with with (union_with (M := option NZA))
  by reflexivity.
  match goal with
  |- merge ?e ?x ?y = merge ?e ?y ?x => set (f := e)
  end.
  apply (merge_comm' f).
  clear poly x y.
  cbv [f]. clear f.
  match goal with
  |- Comm eq (union_with ?e) => set (g := e)
  end.
  apply (option.union_with_comm g).
  intros a b.
  cbv [g]. clear g.
  destruct (decide (`a + `b <> 0)%ring) as [Fab | Fab],
  (decide (`b + `a <> 0)%ring) as [Fba | Fba].
  - f_equal. apply sig_eq_pi; [typeclasses eauto |].
    cbn. rewrite comm. reflexivity.
  - exfalso. apply Fba. rewrite comm...
    apply Fab.
  - exfalso. apply Fab. rewrite comm...
    apply Fba.
  - reflexivity. Defined.

Global Instance poly_bin_op_is_comm_sgrp : IsCommSgrp poly bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_is_l_unl : IsLUnl poly bin_op null_op.
Proof.
  intros x. cbv [bin_op poly_has_bin_op poly_add
  null_op poly_zero poly_has_null_op].
  cbv [union_with map_union_with].
  replace option_union_with with (union_with (M := option NZA))
  by reflexivity.
  match goal with
  |- merge ?e ?x ?y = ?z => set (f := e)
  end.
  apply (left_id empty (merge f)). Defined.

Global Instance poly_bin_op_null_op_is_r_unl : IsRUnl poly bin_op null_op.
Proof.
  intros x. cbv [bin_op poly_has_bin_op poly_add
  null_op poly_zero poly_has_null_op].
  cbv [union_with map_union_with].
  replace option_union_with with (union_with (M := option NZA))
  by reflexivity.
  match goal with
  |- merge ?e ?x ?y = ?z => set (f := e)
  end.
  apply (right_id empty (merge f)). Defined.

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
