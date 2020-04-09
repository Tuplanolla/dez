(* bad *)
From Coq Require Import
  Lists.List Logic.ProofIrrelevance ZArith.ZArith.
From Maniunfold.Has Require Export
  OneSorted.Enumeration OneSorted.Cardinality TwoSorted.Isomorphism.
From Maniunfold.Is Require Export
  OneSorted.Finite TwoSorted.Isomorphism TwoSorted.Bimodule
  OneSorted.Ring TwoSorted.UnitalAssociativeAlgebra TwoSorted.Graded.Algebra.
From Maniunfold.Offers Require Export
  TwoSorted.IsomorphismMappings NaturalPowers.
From Maniunfold.Provides Require Export
  ZTheorems.
From Maniunfold.ShouldHave Require Import
  OneSorted.ArithmeticNotations.
From Maniunfold.ShouldOffer Require Import
  IntegerPowerNotations.

Import ListNotations.

Local Open Scope N_scope.

Fixpoint Nseq (start len : N) : list N :=
  map N.of_nat (seq (N.to_nat start) (N.to_nat len)).

Section Context.

Context {A B : Type} `{is_two_bimod : IsTwoBimod A B}.

(** We define inhabitants of the tensor algebra in such a way that
    - [0] becomes [Tensor 0 0 _],
    - [2] becomes [Tensor 0 2 _],
    - [(3, 5) x] becomes [Tensor 1 0 (fun n p => (3, 5))],
    - [2 + (3, 5) x] becomes [Tensor 1 2 (fun n p => (3, 5))].
    - [2 + (3, 5) x + ((7, 11), (13, 17), (19, 23)) x^3] becomes
      [Tensor 3 2 (fun n p => match n with
      | 1 => (3, 5)
      | 3 => match p with
        | 0 => (7, 11)
        | 1 => (13, 17)
        | 2 => (19, 23)
        | _ => (0, 0)
        end
      | _ => (0, 0)
      end)]. *)

Record tensor : Type := {
  deg : N;
  ground : A;
  air : N -> N -> B;
  (* air : forall n : deg, n -> B; *)
}.

Definition teqb (p q : tensor) : Prop :=
  deg p = deg q /\ ground p = ground q /\
  forall n : N, n < deg p ->
  forall m : N, m < n ->
  air p m = air q m.

(** Here is a finite version defined in such a way that
    - [0] becomes [Tensor 0 []],
    - [2] becomes [Tensor 2 []],
    - [(3, 5) x] becomes [Tensor 0 [(3, 5)]],
    - [2 + (3, 5) x] becomes [Tensor 2 [(3, 5)]].
    - [2 + (3, 5) x + ((7, 11), (13, 17), (19, 23)) x^3] becomes
      [Tensor 2 [[],
        [(3, 5)],
        [(0, 0), (0, 0)],
        [(7, 11), (13, 17), (19, 23)]]]. *)

Record lensor : Type := {
  heady : A;
  taily : list (list B);
  (* valid : forall n : N, n < length taily -> length (nth n taily) = n; *)
}.

(** TODO Should really use an AVL tree here. *)

Definition leqb (p q : lensor) : Prop :=
  heady p = heady q /\ taily p = taily q.

Arguments combine {_ _}.

Definition Add (p q : lensor) : lensor :=
  match p, q with
  | {| heady := x; taily := xs |}, {| heady := y; taily := ys |} =>
    {| heady := add x y; taily := map (fun (xys : list B * list B) =>
        map (fun (xy : B * B) => add (fst xy) (snd xy)) (uncurry combine xys))
      (combine xs ys) |}
  end.

Definition Zero : lensor :=
  {| heady := 0; taily := [] |}.

Definition Neg (p : lensor) : lensor :=
  match p with
  | {| heady := x; taily := xs |} =>
    {| heady := x; taily := map (map neg) xs |}
  end.

Definition LAct (a : A) (p : lensor) : lensor :=
  match p with
  | {| heady := x; taily := xs |} =>
    {| heady := x; taily := map (map (l_act a)) xs |}
  end.

Definition RAct (p : lensor) (a : A) : lensor :=
  match p with
  | {| heady := x; taily := xs |} =>
    {| heady := x; taily := map (map (flip r_act a)) xs |}
  end.

Arguments app {_}.

(** TODO This product is wrong. *)

Definition GrdBinFn (p q : lensor) : lensor :=
  match p, q with
  | {| heady := x; taily := xs |}, {| heady := y; taily := ys |} =>
    {| heady := mul x y; taily := map (fun (xys : list B * list B) =>
        uncurry app xys)
      (combine xs ys) |}
  end.

Definition GrdMul (p q : A) : A := mul p q.

Definition GrdOne : A := one.

Global Instance N_has_bin_op : HasBinOp N := N.add.

Global Instance N_has_null_op : HasNullOp N := N.zero.

Check IsGrdAlg (A := N) (fun n : N => A) (fun n : N => lensor)
  (A_has_bin_op := N_has_bin_op) (A_has_null_op := N_has_null_op)
  (fun n : N => Addition.add) (fun n : N => zero) (fun n : N => neg)
  (fun n p : N => GrdMul) GrdOne
  (fun n : N => Add) (fun n : N => Zero) (fun n : N => Neg)
  (fun n p : N => GrdBinFn)
  (fun n p : N => LAct) (fun n p : N => RAct).

(** Instant tensor algebra; just add water. *)

Global Instance lensor_is_grd_alg :
  IsGrdAlg (A := N) (fun n : N => A) (fun n : N => lensor)
  (A_has_bin_op := N_has_bin_op) (A_has_null_op := N_has_null_op)
  (fun n : N => Addition.add) (fun n : N => zero) (fun n : N => neg)
  (fun n p : N => GrdMul) GrdOne
  (fun n : N => Add) (fun n : N => Zero) (fun n : N => Neg)
  (fun n p : N => GrdBinFn)
  (fun n p : N => LAct) (fun n p : N => RAct).
Proof. repeat split. Abort.

End Context.

Section Tests.

Local Open Scope Z_scope.

Let p := Build_lensor 2 [[];
  [(0, 0, 0)];
  [(1, 0, 0); (1, 0, 0)];
  [(0, 0, 7); (0, 1, 0); (1, 0, 0)]].

Let q := Build_lensor 2 [[];
  [(2, 1, 0)];
  [(0, 0, 0); (0, 0, 0)];
  [(0, 1, 0); (0, 1, 0); (0, 0, 1)]].

Let r := Build_lensor 2 [[];
  [(0, 0, 0)];
  [(0, 0, 0); (0, 0, 0)];
  [(1, 0, 0); (1, 0, 0); (2, 1, 0)];
  [(0, 0, 7); (0, 1, 0); (1, 0, 0); (2, 1, 0)];
  [(1, 0, 0); (1, 0, 0); (0, 1, 0); (0, 1, 0); (0, 0, 1)];
  [(0, 0, 7); (0, 1, 0); (1, 0, 0); (0, 1, 0); (0, 1, 0); (0, 0, 1)]].

Compute GrdBinFn p q.
Compute r.

End Tests.
