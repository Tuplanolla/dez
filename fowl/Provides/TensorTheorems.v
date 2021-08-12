(* bad *)
From Coq Require Import
  Lists.List Logic.ProofIrrelevance ZArith.ZArith.
From DEZ.Has Require Export
  OneSortedEnumeration OneSortedCardinality.
From DEZ.Is Require Export
  OneSortedFinite Isomorphism TwoSortedBimodule
  Ring TwoSortedUnitalAssociativeAlgebra.
From DEZ.Offers Require Export
  OneSortedPositiveOperations OneSortedNaturalOperations
  OneSortedIntegerOperations.
From DEZ.Provides Require Export
  ZTheorems.
From DEZ.ShouldHave Require Import
  OneSortedArithmeticNotations.
From DEZ.ShouldOffer Require Import
  OneSortedMultiplicativeOperationNotations.

Import ListNotations.

Import Addition.Subclass Zero.Subclass Negation.Subclass
  Multiplication.Subclass One.Subclass.

Definition Nseq (start len : N) : list N :=
  map N.of_nat (seq (N.to_nat start) (N.to_nat len)).

(* From Coq Require Import
  FSets.FMapAVL Structures.OrderedTypeEx.
Module Import Map := FMapAVL.Make Positive_as_OT. *)

From Coq Require Import
  FSets.FMapList Structures.OrderedTypeEx.
Module Import Map := FMapList.Make Positive_as_OT.

From Coq Require Import
  FSets.FMapFacts.

Module Props := WProperties_fun Positive_as_OT Map.
Module Mapper := Props.F.

Definition Map_max_key {A : Type} (xs : Map.t A) : option key :=
  Map.fold (fun (n : key) (x : A) (ms : option key) =>
    match ms with
    | Some m => Some (Pos.max n m)
    | None => Some n
    end) xs None.

Definition Map_max_key_def {A : Type} (d : key) (xs : Map.t A) : key :=
  Map.fold (fun (n : key) (x : A) (m : key) => Pos.max n m) xs d.

Section Context.

Context (A B : Type) `{IsTwoBimod A B}.

Record tensor : Type := {
  ht : A;
  tt : Map.t (list B);
}.

Definition proper (p : tensor) : Prop :=
  forall (k : key) (x : list B),
  MapsTo k x (tt p) -> length x = Pos.to_nat k.

Definition Add (p q : tensor) : tensor := {|
  ht := Addition.add (ht p) (ht q);
  tt := Map.map2 (fun (as' bs : option (list B)) => match as', bs with
    | Some a, Some b => Some (List.map (prod_uncurry Addition.add) (combine a b))
    | Some a, None => Some a
    | None, Some b => Some b
    | None, None => None
    end) (tt p) (tt q)
|}.

Definition Zero : tensor := {|
  ht := zero;
  tt := Map.empty (list B);
|}.

Definition Neg (p : tensor) : tensor :={|
  ht := neg (ht p);
  tt := Map.map (List.map neg) (tt p);
|}.

Definition ActL (a : A) (p : tensor) : tensor :=
  {| ht := ht p; tt := Map.map (List.map (act_l a)) (tt p) |}.

Definition ActR (p : tensor) (a : A) : tensor :=
  {| ht := ht p; tt := Map.map (List.map (flip act_r a)) (tt p) |}.

Global Instance N_has_bin_op : HasBinOp N := N.add.

Global Instance N_has_null_op : HasNullOp N := N.zero.

(** Instant tensor algebra; just add water. *)

End Context.

(* Section Tests.

Local Open Scope Z_scope.

Instance positive_has_one : HasOne positive := xH.

Instance Z3_has_add : HasAdd (Z * Z * Z) :=
  fun x y : Z * Z * Z =>
  match x, y with
  | (x0, x1, x2), (y0, y1, y2) => (x0 + y0, x1 + y1, x2 + y2)
  end.

Instance Z3_has_neg : HasNeg (Z * Z * Z) :=
  fun x : Z * Z * Z =>
  match x with
  | (x0, x1, x2) => (- x0, - x1, - x2)
  end.

Instance Z3_has_act_l : HasActL Z (Z * Z * Z) :=
  fun (a : Z) (x : Z * Z * Z) =>
  match x with
  | (x0, x1, x2) => (a * x0, a * x1, a * x2)
  end.

Instance Z3_has_act_r : HasActR Z (Z * Z * Z) :=
  fun (x : Z * Z * Z) (a : Z) =>
  match x with
  | (x0, x1, x2) => (x0 * a, x1 * a, x2 * a)
  end.

Let p : tensor := {|
  ht := Z.zero;
  tt := Props.of_list [
    (1%positive, [(0, 0, 0)]);
    (2%positive, [(1, 0, 0); (1, 0, 0)]);
    (3%positive, [(0, 0, 7); (0, 1, 0); (1, 0, 0)])];
|}.

Let q : tensor := {|
  ht := Z.zero;
  tt := Props.of_list [
    (1%positive, [(2, 1, 0)]);
    (2%positive, [(1, 0, 0); (1, 0, 0)]);
    (3%positive, [(0, 1, 0); (0, 1, 0); (0, 0, 1)])];
|}.

Let r : tensor := {|
  ht := Z.zero;
  tt := Props.of_list [
    (1%positive, [(0, 0, 0)]);
    (2%positive, [(0, 0, 0); (0, 0, 0)]);
    (3%positive, [(1, 0, 0); (1, 0, 0); (2, 1, 0)]);
    (4%positive, [(0, 0, 7); (0, 1, 0); (1, 0, 0); (2, 1, 0)]);
    (5%positive, [(1, 0, 0); (1, 0, 0); (0, 1, 0); (0, 1, 0); (0, 0, 1)]);
    (6%positive, [(0, 0, 7); (0, 1, 0); (1, 0, 0); (0, 1, 0); (0, 1, 0); (0, 0, 1)])];
|}.

Compute GrdMul p q.
Compute r.

End Tests. *)
