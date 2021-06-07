(* bad *)
From Coq Require Import
  Lists.List Logic.ProofIrrelevance ZArith.ZArith.
From Maniunfold.Has Require Export
  OneSortedEnumeration OneSortedCardinality.
From Maniunfold.Is Require Export
  OneSortedFinite Isomorphism TwoSortedBimodule
  OneSortedRing TwoSortedUnitalAssociativeAlgebra TwoSortedGradedAlgebra.
From Maniunfold.Offers Require Export
  OneSortedPositiveOperations OneSortedNaturalOperations
  OneSortedIntegerOperations.
From Maniunfold.Provides Require Export
  ZTheorems.
From Maniunfold.ShouldHave Require Import
  OneSortedArithmeticNotations.
From Maniunfold.ShouldOffer Require Import
  OneSortedMultiplicativeOperationNotations.

Import ListNotations.

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
  ht := OneSortedAddition.add (ht p) (ht q);
  tt := Map.map2 (fun (as' bs : option (list B)) => match as', bs with
    | Some a, Some b => Some (List.map (prod_uncurry OneSortedAddition.add) (combine a b))
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

(** TODO This is still wrong. *)

Definition GrdMul (ps qs : tensor) : tensor :=
  match ps, qs with
  | {| ht := pp; tt := p |}, {| ht := qq; tt := q |} => {| ht := pp * qq; tt :=
    fold_right (fun (k : nat) (r : t (list B)) =>
      fold_right (fun (l : nat) (s : t (list B)) => match Map.find (Pos.of_nat k) s with
        | Some u => Map.add (Pos.of_nat k) (app u
          match Map.find (Pos.of_nat l) p, Map.find (Pos.of_nat (Nat.sub k l)) q with
          | Some a, Some b => app a b (* List.map (prod_curry OneSortedAddition.add) (combine a b) *)
          | _, _ => nil
          end) s
        | None => Map.add (Pos.of_nat k)
          match Map.find (Pos.of_nat l) p, Map.find (Pos.of_nat (Nat.sub k l)) q with
          | Some a, Some b => app a b
          | _, _ => nil
          end s
        end)
      r (seq (S O) k))
    (Map.empty (list B))
    (seq (S O) (Pos.to_nat (Pos.add (Map_max_key_def xH p) (Map_max_key_def xH q)))) |}
  end.

Definition GrdOne : tensor :=
  {| ht := one; tt := Map.empty (list B) |}.

Definition LAct (a : A) (p : tensor) : tensor :=
  {| ht := ht p; tt := Map.map (List.map (l_act a)) (tt p) |}.

Definition RAct (p : tensor) (a : A) : tensor :=
  {| ht := ht p; tt := Map.map (List.map (flip r_act a)) (tt p) |}.

Global Instance N_has_bin_op : HasBinOp N := N.add.

Global Instance N_has_null_op : HasNullOp N := N.zero.

(** Instant tensor algebra; just add water. *)

Global Instance lensor_is_grd_alg :
  IsGrdAlg (A := N) (P := fun n : N => A) (Q := fun n : N => tensor)
  (N_has_bin_op) (N_has_null_op)
  (fun n : N => OneSortedAddition.add) (fun n : N => zero) (fun n : N => neg)
  (fun n p : N => mul) one
  (fun n : N => Add) (fun n : N => Zero) (fun n : N => Neg)
  (fun n p : N => GrdMul)
  (fun n p : N => LAct) (fun n p : N => RAct).
Proof. repeat split. Abort.

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

Instance Z3_has_l_act : HasLAct Z (Z * Z * Z) :=
  fun (a : Z) (x : Z * Z * Z) =>
  match x with
  | (x0, x1, x2) => (a * x0, a * x1, a * x2)
  end.

Instance Z3_has_r_act : HasRAct Z (Z * Z * Z) :=
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
