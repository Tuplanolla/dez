(* bad *)
From Coq Require Import
  ZArith.ZArith.
From stdpp Require Import
  option gmap pmap nmap.
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
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.
From Maniunfold.ShouldOffer Require Import
  OneSorted.ArithmeticOperationNotations.

(** TODO Use this mess for something, such as demonstrating graded algebras. *)

Section Context.

Context {A : Type} `{is_ring : IsRing A}.

Definition poly : Type := Nmap A.

Definition poly_eval (p : poly) (x : A) : A :=
  map_fold (fun (i : N) (a b : A) => b + a * (x ^ i)%N) 0 p.

(** Parallel sum.
    The terms of $p$, $q$ and $r$ in $r = p + q$ are related
    by $r_k = p_k + q_k$. *)

Definition poly_add (p q : poly) : poly :=
  merge (fun as' bs : option A =>
    union_with (fun a b : A => Some (a + b)) as' bs) p q.

Definition poly_zero : poly :=
  empty.

Definition poly_neg (p : poly) : poly :=
  fmap (fun a : A => - a) p.

(** Discrete convolution.
    The terms of $p$, $q$ and $r$ in $r = p \times q$ are related
    by $r_k = \sum_{i + j = k} p_i \times q_j$. *)

Definition poly_mul (p q : poly) : poly :=
  map_fold (fun (i : N) (a : A) (r : poly) =>
    map_fold (fun (j : N) (b : A) (s : poly) =>
      partial_alter (fun cs : option A =>
        Some (a * b + default 0 cs)) (i + j) s) r q) empty p.

Definition poly_one : poly :=
  singletonM 0 1.

Definition poly_l_act (a : A) (p : poly) : poly :=
  fmap (fun b : A => a * b) p.

Definition poly_r_act (p : poly) (a : A) : poly :=
  fmap (fun b : A => b * a) p.

End Context.

Module Additive.

Section Context.

Context {A : Type} `{is_ring : IsRing A}.

Let poly := poly (A := A).

Global Instance poly_has_bin_op : HasBinOp poly := poly_add.
Global Instance poly_has_null_op : HasNullOp poly := poly_zero.
Global Instance poly_has_un_op : HasUnOp poly := poly_neg.

Global Instance poly_bin_op_is_mag : IsMag poly bin_op.
Proof. Defined.

Global Instance poly_bin_op_is_assoc : IsAssoc poly bin_op.
Proof. intros x y z. Admitted.

Global Instance poly_bin_op_is_sgrp : IsSgrp poly bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_is_comm : IsComm poly bin_op.
Proof. intros x y. Admitted.

Global Instance poly_bin_op_is_comm_sgrp : IsCommSgrp poly bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_is_l_unl : IsLUnl poly bin_op null_op.
Proof. intros x. Admitted.

Global Instance poly_bin_op_null_op_is_r_unl : IsRUnl poly bin_op null_op.
Proof. intros x. Admitted.

Global Instance poly_bin_op_null_op_is_unl : IsUnl poly bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_is_mon : IsMon poly bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_is_comm_mon :
  IsCommMon poly bin_op null_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_un_op_is_l_inv :
  IsLInv poly bin_op null_op un_op.
Proof. intros x. Admitted.

Global Instance poly_bin_op_null_op_un_op_is_r_inv :
  IsRInv poly bin_op null_op un_op.
Proof. intros x. Admitted.

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

Section Context.

Context {A : Type} `{is_ring : IsRing A}.

Let poly := poly (A := A).

Global Instance poly_bin_op_has_bin_op : HasBinOp poly := poly_mul.
Global Instance poly_has_null_op : HasNullOp poly := poly_one.

Global Instance poly_bin_op_is_mag : IsMag poly bin_op.
Proof. Defined.

Global Instance poly_bin_op_is_assoc : IsAssoc poly bin_op.
Proof. intros x y z. Admitted.

Global Instance poly_bin_op_is_sgrp : IsSgrp poly bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_is_comm : IsComm poly bin_op.
Proof. intros x y. Admitted.

Global Instance poly_bin_op_is_comm_sgrp : IsCommSgrp poly bin_op.
Proof. split; typeclasses eauto. Defined.

Global Instance poly_bin_op_null_op_is_l_unl : IsLUnl poly bin_op null_op.
Proof. intros x. Admitted.

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

Section Context.

Context {A : Type} `{is_ring : IsRing A}.

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
  apply merge_comm'.
  - reflexivity.
  - intros [a |] [b |]; cbn.
    + rewrite comm... reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity. Defined.

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

Global Instance add_zero_neg_mul_one_is_unl_assoc_alg :
  IsUnlAssocAlg A poly add zero neg mul one add zero neg mul one l_act r_act.
Proof. repeat split. Abort.

End Context.

Section Tests.

Local Open Scope Z_scope.

(* 42 * x ^ 3 + 7 + 13 * x *)
Let p : poly := insert (N.add N.one N.two) 42
  (insert N.zero 7 (insert N.one 13 empty)).

(* 3 * x ^ 4 + x + 5 *)
Let q : poly := insert (N.add N.two N.two) 3
  (insert N.one 1 (insert N.zero 5 empty)).

(* 7, 5 *)
Compute poly_eval p 0.
Compute poly_eval q 0.
(* 1180, 251 *)
Compute poly_eval p 3.
Compute poly_eval q 3.

(* 12, 1431 *)
Compute poly_eval (add p q) 0.
Compute poly_eval (add p q) 3.

(* 35, 296180 *)
Compute poly_eval (mul p q) 0.
Compute poly_eval (mul p q) 3.

End Tests.
