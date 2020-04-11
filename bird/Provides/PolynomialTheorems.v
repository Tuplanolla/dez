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
