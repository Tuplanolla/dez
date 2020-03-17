From Maniunfold.Has Require Export
  EquivalenceRelation Addition Multiplication.
From Maniunfold.Is Require Export
  Commutative Monoid Distributive Absorbing.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations ArithmeticNotations.

(** This is a unital semiring. *)

Class IsSring {A : Type}
  (has_add : HasAdd A) (has_zero : HasZero A)
  (has_mul : HasMul A) (has_one : HasOne A) : Prop := {
  add_is_comm :> IsComm add;
  add_zero_is_mon :> IsMon add zero;
  add_mul_is_distr :> IsDistr add mul;
  zero_mul_is_absorb :> IsAbsorb zero mul;
  mul_one_is_mon :> IsMon mul one;
}.

(** TODO Recover from this delirium. *)

Module TCS.

Unset Elimination Schemes.

Inductive t : Type :=
  | and : t
  | or : t
  | into : t
  | thanks : t.

End TCS.

Ltac tcs x y :=
  change x with y in *.

(** Accumulator, in Haskell. *)
(*  let {
      r :: [Char] -> [Char] -> [[Char]]
      r [] ys = [ys];
      r (',' : xs) ys = ys : r xs [];
      r (x : xs) ys = r xs (x : ys)} in
    r "yes,no" [] -- ["sey","on"] *)
(** Single continuation, in Haskell. *)
(*  let {
      r :: [Char] -> ([Char] -> [[Char]]) -> [[Char]]
      r [] k = k []
      r (',' : xs) k = r xs (\ ys -> ys : k [])
      r (x : xs) k = r xs (\ ys -> k (x : ys))} in
    r "yes,no" (\ ys -> [ys]) -- ["no","yes"] *)
(** Double continuation, in Haskell. *)
(*  let {
      r :: [Char] -> ([Char] -> [[Char]] -> [[Char]]) -> [[Char]]
      r [] k = k [] []
      r (',' : xs) k = r xs (\ ys zs -> k [] (ys : zs))
      r (x : xs) k = r xs (\ ys zs -> k (x : ys) zs)} in
    r "yes,no" (\ ys zs -> ys : zs) -- ["yes","no"] *)

(** Polished, in Haskell. *)
(*  r :: Eq a => a -> [a] -> ([a] -> [[a]] -> [[a]]) -> [[a]]
    r c [] k = k [] []
    r c (x : xs) k = if x == c then
      r c xs (\ ys zs -> k [] (ys : zs)) else
      r c xs (\ ys zs -> k (x : ys) zs) *)
(** Fused, in Haskell. *)
(*  ff c d ws = let
      r k [] = k [] []
      r k (x : xs) = if x == c then
        r (\ ys zs -> k [] (let
          fr k [] = k [] []
          fr k (x : xs) = if x == d then
            fr (\ ys zs -> k [] (ys : zs)) xs else
            fr (\ ys zs -> k (x : ys) zs) xs in
          fr (:) ys : zs)) xs else
            r (\ ys zs -> k (x : ys) zs) xs in
      r (\ ys zs -> let
          fr k [] = k [] []
          fr k (x : xs) = if x == d then
            fr (\ ys zs -> k [] (ys : zs)) xs else
            fr (\ ys zs -> k (x : ys) zs) xs in
          fr (:) ys : zs) ws *)

(** Reverse list. *)

Ltac reverse_aux k xs :=
  match xs with
  | tt => k
  | ?i => (fun xs => reverse_aux ltac:(exact (@cons bool i ltac:(k))) xs)
  end.

Ltac reverse xs := reverse_aux ltac:(exact (@nil bool)) xs.

Goal True. Proof. set (x := ltac:(reverse tt)). Abort.
Goal True. Proof. set (x := ltac:(reverse false true false false tt)). Abort.

(** Nonreverse list. *)

Ltac direct_aux k xs :=
  match xs with
  | tt => exact (ltac:(k) (@nil bool))
  | ?i => (fun xs => direct_aux
    ltac:(exact (fun ys : list bool => ltac:(k) (@cons bool i ys))) xs)
  end.

Ltac direct xs := direct_aux ltac:(exact (fun ys : list bool => ys)) xs.

Goal True. Proof. set (x := ltac:(direct tt)). Abort.
Goal True. Proof. set (x := ltac:(direct false true false false tt));
  cbn in x. Abort.

(** Split list. *)

Ltac recs k xs :=
  match xs with
  | False => exact (ltac:(k) nil nil)
  | True => (fun xs => recs ltac:(exact (fun ys zs => ltac:(k) nil (cons ys zs))) xs)
  | ?x => (fun xs => recs ltac:(exact (fun ys zs => ltac:(k) (cons x ys) zs)) xs)
  end.

Fail Fail Ltac rec xs := recs ltac:(exact (fun ys zs => cons ys zs)) xs.
Ltac rec xs := recs ltac:(exact (fun (ys : list bool) (zs : list (list bool)) =>
  cons ys zs)) xs.

Goal True. Proof. set (y := ltac:(rec False)); cbn in y.
  set (x := ltac:(rec false true True false false False)); cbn in x.
Abort.

(** Interpreting the split list. *)

Ltac jams k xs :=
  match xs with
  | tt => (fun xs => jams k xs)
  | False => exact (ltac:(k) nil nil)
  | True => (fun xs => jams ltac:(exact (fun ys zs => ltac:(k) nil (cons ys zs))) xs)
  | ?x => (fun xs => jams ltac:(exact (fun ys zs => ltac:(k) (cons x ys) zs)) xs)
  end.

Fail Fail Ltac jam xs := jams ltac:(exact (fun ys zs => cons ys zs)) xs.
Ltac jam xs := jams ltac:(exact (fun (ys : list bool) (zs : list (list bool)) =>
  cons ys zs)) xs.

Goal True. Proof. set (y := ltac:(jam False)); cbn in y.
  set (x := ltac:(jam false tt tt tt true True false false False)); cbn in x.
Abort.

Ltac unjam xs :=
  match xs with
  | nil => idtac
  | cons (cons ?x (cons ?y nil)) ?ys => idtac "change" x "with" y; unjam ys
  | ?w => fail "Invalid argument" w
  end.

Goal True. Proof.
  set (x := ltac:(
    jam false tt tt tt true True false false False)); cbn in x.
  let y := eval unfold x in x in unjam y.
Abort.

(** Now put the jams together. *)

(** Now repeat for the fused definition. *)

(** Wrap with tactic notations. *)

(* Ltac specializations := typeclasses specialize
  bin_op into add and null_op into zero or
  bin_op into mul and null_op into one. *)

Section Context.

Context {A : Type} `{is_sring : IsSring A}.

Ltac specializations :=
  typeclasses specialize bin_op into add, null_op into zero ||
  typeclasses specialize bin_op into mul, null_op into one ||
  fail "Nothing to specialize".

Goal 0 = 1 -> forall x y : A, x = y.
Proof with specializations.
  intros H x y.
  rewrite <- (l_unl (A_has_null_op := 1) x)...
  rewrite <- (l_unl (A_has_null_op := 1) y)...
  rewrite <- H.
  rewrite (l_absorb x).
  rewrite (l_absorb y).
  reflexivity. Qed.

End Context.
