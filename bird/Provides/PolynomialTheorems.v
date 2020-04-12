(* bad *)
From Coq Require Import
  Lists.List Logic.ProofIrrelevance ZArith.ZArith.
From Maniunfold.Has Require Export
  OneSorted.Enumeration OneSorted.Cardinality TwoSorted.Isomorphism.
From Maniunfold.Is Require Export
  OneSorted.Finite TwoSorted.Isomorphism
  OneSorted.Ring TwoSorted.UnitalAssociativeAlgebra TwoSorted.Graded.Algebra.
From Maniunfold.Offers Require Export
  TwoSorted.IsomorphismMappings
  OneSorted.PositiveOperations OneSorted.NaturalOperations
  OneSorted.IntegerOperations.
From Maniunfold.Provides Require Export
  ZTheorems.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.
From Maniunfold.ShouldOffer Require Import
  OneSorted.MultiplicativeOperationNotations.

(** TODO Use this mess for something, such as demonstrating graded algebras. *)

Import ListNotations.

Fixpoint Nseq (start len : N) : list N :=
  map N.of_nat (seq (N.to_nat start) (N.to_nat len)).

(* From Coq Require Import
  FSets.FMapAVL Structures.OrderedTypeEx.
Module Import Map := FMapAVL.Make N_as_OT. *)

From Coq Require Import
  FSets.FMapList Structures.OrderedTypeEx.
Module Import Map := FMapList.Make N_as_OT.

From Coq Require Import
  FSets.FMapFacts.

Module Props := WProperties_fun N_as_OT Map.
Module Mapper := Props.F.

Definition Map_max_key {A : Type} (xs : Map.t A) : option N :=
  Map.fold (fun (n : N) (x : A) (ms : option N) =>
    match ms with
    | Some m => Some (N.max n m)
    | None => Some n
    end) xs None.

Definition Map_max_key_def {A : Type} (d : N) (xs : Map.t A) : N :=
  Map.fold (fun (n : N) (x : A) (m : N) => N.max n m) xs d.

Section Context.

Context {A : Type} `{is_ring : IsRing A}.

Definition poly : Type := Map.t A.

Definition eval (p : poly) (x : A) : A :=
  Map.fold (fun (n : N) (a y : A) => y + a * (x ^ n)%N) p 0.

Definition Add (p q : poly) : poly :=
  Map.map2 (fun (as' bs : option A) => match as', bs with
  | Some a, Some b => Some (a + b)
  | Some a, None => Some a
  | None, Some b => Some b
  | None, None => None
  end) p q.

Definition Zero : poly :=
  Map.empty A.

Definition Neg (p : poly) : poly :=
  Map.map neg p.

Definition Mul (p q : poly) : poly :=
  fold_right (fun (k : nat) (r : poly) =>
    fold_right (fun (l : nat) (s : poly) => match Map.find (N.of_nat k) s with
      | Some u => Map.add (N.of_nat k) (u +
        match Map.find (N.of_nat l) p, Map.find (N.of_nat (Nat.sub k l)) q with
        | Some a, Some b => a * b
        | _, _ => 0
        end) s
      | None => Map.add (N.of_nat k)
        match Map.find (N.of_nat l) p, Map.find (N.of_nat (Nat.sub k l)) q with
        | Some a, Some b => a * b
        | _, _ => 0
        end s
      end)
    r (seq O (S k)))
  (Map.empty A)
  (seq O (S (N.to_nat (N.add (Map_max_key_def N0 p) (Map_max_key_def N0 q))))).

Definition One : poly :=
  Map.add N.zero one (Map.empty A).

Definition LAct (a : A) (p : poly) : poly :=
  Map.map (mul a) p.

Definition RAct (p : poly) (a : A) : poly :=
  Map.map (flip mul a) p.

Global Instance poly_has_add : HasAdd poly := Add.

Global Instance poly_has_zero : HasZero poly := Zero.

Global Instance poly_has_neg : HasNeg poly := Neg.

Global Instance poly_has_mul : HasMul poly := Mul.

Global Instance poly_has_one : HasOne poly := One.

Global Instance poly_has_l_act : HasLAct A poly := LAct.

Global Instance poly_has_r_act : HasRAct A poly := RAct.

Axiom FMap_extensionality : forall {A : Type} (m n : t A),
  m = n <-> Equal m n.

Global Instance add_is_assoc : IsAssoc poly Addition.add.
Proof.
  intros p q r. cbv [bin_op Addition.add poly_has_add].
  apply FMap_extensionality. induction p using Props.map_induction_bis.
  - cbn. apply FMap_extensionality in H. rewrite <- H. apply IHp1.
  - Abort.

Global Instance add_zero_neg_mul_one_is_ring :
  IsRing poly Add Zero Neg Mul One.
Proof. repeat split. all: cbv -[Map.t Add Zero Neg Mul One]. Abort.

Global Instance add_zero_neg_mul_one_is_ring :
  IsUnlAssocAlg A poly Addition.add zero neg mul one
  Add Zero Neg Mul One LAct RAct.
Proof. repeat split. all: cbv -[Map.t Add Zero Neg Mul One LAct RAct]. Abort.

Global Instance N_has_bin_op : HasBinOp N := N.add.

Global Instance N_has_null_op : HasNullOp N := N.zero.

Global Instance poly_is_grd_ring : IsGrdRing (A := N) (fun n : N => A)
  (fun n : N => Addition.add) (fun n : N => zero) (fun n : N => neg)
  (fun n p : N => mul) one.
Proof. repeat split. Abort.

End Context.

(** We would like these equalities to hold definitionally. *)

(* 0 = 0 * x = 0 + 0 * x *)
(* x = 1 * x = 0 + 1 * x *)
(* x^2 = 1 * x^2 = 0 + 0 * x + 1 * x^2 *)

Local Open Scope N_scope.
Local Open Scope Z_scope.

(** Here are some tests. *)

Section Tests.

(* 0 *)
Compute Map.empty Z.
(* 42 = 42 + x \times (0) *)
Compute Map.add N.zero 42 (Map.empty Z).
(* 13 + 42 \times x = 13 + x \times (42) *)
Compute Map.add N.one 42 (Map.add N.zero 13 (Map.empty Z)).
(* 7 + 13 \times x + 42 \times x^3 = 7 + x \times (13 + 42 \times x^2) *)
Compute Map.add (N.add N.one N.two) 42
  (Map.add N.zero 7 (Map.add N.one 13 (Map.empty Z))).

(* 42 * x ^ 3 + 7 + 13 * x *)
Let p := Map.add (N.add N.one N.two) 42
  (Map.add N.zero 7 (Map.add N.one 13 (Map.empty Z))).

(* 3 * x ^ 4 + x + 5 *)
Let q := Map.add (N.add N.two N.two) 3
  (Map.add N.one 1 (Map.add N.zero 5 (Map.empty Z))).

(* 7, 5 *)
Compute eval p 0.
Compute eval q 0.
(* 1180, 251 *)
Compute eval p 3.
Compute eval q 3.

(* 12, 1431 *)
Compute eval (Add p q) 0.
Compute eval (Add p q) 3.

(* 35, 296180 *)
Compute eval (Mul p q) 0.
Compute eval (Mul p q) 3.

End Tests.

(** TODO Try Leibniz maps from std++. *)

From Coq Require Import
  FunctionalExtensionality.
From stdpp Require Import
  option gmap pmap nmap.
From Maniunfold.Provides Require Import
  NTheorems.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.
From Maniunfold.ShouldOffer Require Import
  OneSorted.MultiplicativeOperationNotations.

Module QuiteNice.

Section Context.

Context {A : Type} `{is_ring : IsRing A}.

Definition poly : Type := Nmap A.

Definition poly_eval (p : poly) (x : A) : A :=
  map_fold (fun (i : N) (a b : A) => b + a * x ^ i) 0 p.

Definition poly_add (p q : poly) : poly :=
  map_zip_with add p q.

Definition poly_zero : poly :=
  empty.

Definition poly_neg (p : poly) : poly :=
  fmap neg p.

(** Discrete convolution.
    We have $c_n = \sum_{i + j = n} a_i \times b_j$. *)

Definition poly_mul (p q : poly) : poly :=
  map_fold (fun (i : N) (a : A) (r : poly) =>
    map_fold (fun (j : N) (b : A) (s : poly) =>
      partial_alter (fun cs : option A =>
        Some (match cs with
        | Some c => c
        | None => 0
        end + a * b)) (i + j) s) r q) empty p.

Definition poly_one : poly :=
  singletonM 0 1.

Definition poly_l_act (a : A) (p : poly) : poly :=
  fmap (mul a) p.

Definition poly_r_act (p : poly) (a : A) : poly :=
  fmap (flip mul a) p.

Global Instance poly_has_add : HasAdd poly := poly_add.

Global Instance poly_has_zero : HasZero poly := poly_zero.

Global Instance poly_has_neg : HasNeg poly := poly_neg.

Global Instance poly_has_mul : HasMul poly := poly_mul.

Global Instance poly_has_one : HasOne poly := poly_one.

Global Instance poly_has_l_act : HasLAct A poly := poly_l_act.

Global Instance poly_has_r_act : HasRAct A poly := poly_r_act.

Lemma flip_comm : forall (f : A -> A -> A) {is_comm : IsComm A f},
  flip f = f.
Proof.
  intros f ?. extensionality x. extensionality y.
  cbv [flip]. apply comm. Defined.

Global Instance add_is_comm : IsComm poly add.
Proof.
  intros p q. cbv [bin_op Addition.add poly_has_add].
  cbv [poly_add]. rewrite <- map_zip_with_flip.
  rewrite flip_comm by typeclasses eauto. reflexivity. Defined.

Global Instance add_is_assoc : IsAssoc poly add.
Proof.
  intros p q r. cbv [bin_op Addition.add poly_has_add]. cbv [poly_add]. Abort.

Global Instance add_is_l_unl : IsLUnl poly bin_op one.
Proof. Abort.

Global Instance add_zero_neg_mul_one_is_ring :
  IsRing poly add zero neg mul one.
Proof. repeat split. Abort.

Global Instance add_zero_neg_mul_one_is_unl_assoc_alg :
  IsUnlAssocAlg A poly add zero neg mul one add zero neg mul one l_act r_act.
Proof. repeat split. Abort.

Global Instance poly_is_grd_ring : IsGrdRing (fun i : N => A)
  (fun i : N => Addition.add) (fun i : N => zero) (fun i : N => neg)
  (fun i j : N => mul) one.
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

End QuiteNice.
