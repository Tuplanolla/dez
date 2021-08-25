From Coq Require Import Lists.List Program.Basics Program.Wf.

Import ListNotations.

(** Is this Herbrandization? *)

Set Warnings "-notation-incompatible-format".
Set Implicit Arguments.
Set Maximal Implicit Insertion.

#[local] Open Scope bool_scope.

Inductive term : Set :=
  | var (n : nat) : term
  | un (n : nat) (x : term) : term
  | bin (n : nat) (x y : term) : term
  | rel (x y : term) : term.

Scheme Equality for term.

Fixpoint wf_fix (b : bool) (x : term) : bool :=
  match x with
  | var _ => b
  | un _ x => wf_fix b x
  | bin _ x y => wf_fix b x && wf_fix b y
  | rel x y => if b then false else wf_fix true x && wf_fix true y
  end.

Definition wf (x : term) : bool :=
  wf_fix false x.

Compute wf (rel (bin 0 (var 0) (var 1)) (var 0)).

Fixpoint occurs (n : nat) (x : term) : bool :=
  match x with
  | var p => nat_beq n p
  | un _ x => occurs n x
  | bin _ x y => occurs n x || occurs n y
  | rel x y => occurs n x || occurs n y
  end.

Fixpoint bsub (x y : term) : bool :=
  term_beq x y ||
  match x, y with
  | var n, y => negb (occurs n y)
  | un n x, un p y => nat_beq n p && bsub x y
  | bin n x y, bin p z w => nat_beq n p && bsub x z && bsub y w
  | rel x y, rel z w => bsub x z && bsub y w
  | _, _ => false
  end.

Definition sub (x y : term) : Prop :=
  is_true (bsub x y).

Compute bsub
  (var 0)
  (rel (var 2) (var 0)).

Compute bsub
  (rel (var 2) (var 0))
  (rel (bin 0 (var 0) (var 1)) (var 0)).

Compute bsub
  (rel (var 1) (var 0))
  (rel (bin 0 (var 0) (var 1)) (var 0)).

Class HasMap (F : Type -> Type) : Type :=
  map (A B : Type) (f : A -> B) (x : F A) : F B.

Arguments map {_ _ _ _} _ _.

Class HasPure (F : Type -> Type) : Type :=
  pure (A : Type) (x : A) : F A.

Arguments pure {_ _ _} _.

Class HasJoin (F : Type -> Type) : Type :=
  join (A : Type) (x : F (F A)) : F A.

Arguments join {_ _ _} _.

Class HasBind (F : Type -> Type) : Type :=
  bind (A B : Type) (f : A -> F B) (x : F A) : F B.

Arguments bind {_ _ _ _} _ _.

Notation "x '>>=' f" := (bind f x) (at level 20).

#[local] Instance list_has_map : HasMap list := @List.map.

Definition list_pure (A : Type) (x : A) : list A :=
  [x].

#[local] Instance list_has_pure : HasPure list := @list_pure.

Fixpoint list_join (A : Type) (x : list (list A)) : list A :=
  match x with
  | [] => []
  | a :: y => a ++ list_join y
  end.

#[local] Instance list_has_join : HasJoin list := @list_join.

Definition list_bind (A B : Type) (f : A -> list B) (x : list A) : list B :=
  join (map f x).

#[local] Instance list_has_bind : HasBind list := @list_bind.

Fail Fail Notation "'do' a '<-' x ';' b" := (bind (fun a : _ => b) x)
  (at level 200, a name, x at level 100, b at level 200).

Module IndexedTermNotations.

Notation "'x_' n" := (var n)
  (at level 0, n at level 100, format "'x_' n", only printing).
Notation "'-_' n x" := (un n x)
  (at level 50, format "-_ n  x", only printing).
Notation "x '+_' n y" := (bin n x y)
  (at level 50, format "x  +_ n  y", only printing).
Notation "x '=' y" := (rel x y)
  (at level 70, format "x  =  y", only printing).

End IndexedTermNotations.

Module TermNotations.

Notation "'x'" := (var _)
  (at level 0, format "'x'", only printing).
Notation "'-'' x" := (un _ x)
  (at level 50, format "-'  x", only printing).
Notation "x '+'' y" := (bin _ x y)
  (at level 50, format "x  +'  y", only printing).
Notation "x '=' y" := (rel x y)
  (at level 70, format "x  =  y", only printing).

End TermNotations.

(** Generate all balanced subtrees of depth exactly [m],
    using only one variable. *)

Fail Fail Fixpoint gen (m : nat) : list term :=
  match m with
  | O => [var 0]
  | S m' =>
    gen m' >>= fun y =>
    [un 0 y] ++ (gen m' >>= fun z =>
    [bin 0 y z])
  end.

(** Generate all unbalanced subtrees of depth below [m],
    using only one variable. *)

Fixpoint gen (m : nat) : list term :=
  match m with
  | O => [var 0]
  | S m' =>
    [var 0] ++ (
    gen m' >>= fun y =>
    [un 0 y] ++ (gen m' >>= fun z =>
    [bin 0 y z]))
  end.

Compute gen 0.
Compute gen 1.
Compute gen 2.

Section Context.

Import TermNotations.

Compute gen 0.
Compute gen 1.
Compute gen 2.

End Context.

(** Generate all unbalanced trees of depth below [m],
    using only one variable. *)

Fixpoint gen_fix (b : bool) (m : nat) : list term :=
  match m with
  | O => [var 0]
  | S m' =>
    if b then
    [var 0] ++ (
    gen_fix true m' >>= fun y =>
    [un 0 y] ++ (gen_fix true m' >>= fun z =>
    [bin 0 y z])) else
    gen_fix true m' >>= fun y =>
    gen_fix true m' >>= fun z =>
    [rel y z]
  end.

Definition gen_all (m : nat) : list term :=
  gen_fix false (S m).

Compute gen_all 0.
Compute gen_all 1.
Compute gen_all 2.

(** Replace each occurrence of a variable in a tree with a distinct one,
    following "Reaching for the Star: Tale of a Monad in Coq". *)

Section Context.

Context (St X Y : Type).

(** State carrying three namespaces. *)

Definition State St X := St -> St * X.

Definition run (x : State St X) : St -> X :=
  fun n => snd (x n).

Definition fresh_map (f : X -> Y) (x : State St X) : State St Y :=
  fun n => let (n', x') := x n in (n', f x').

Definition fresh_pure (x : X) : State St X :=
  fun n => (n, x).

Definition fresh_bind (f : X -> State St Y) (m : State St X) : State St Y :=
  fun n => let (n', x) := m n in f x n'.

Record Names : Type := {
  nvar : nat;
  nun : nat;
  nbin : nat;
}.

Definition no_names : Names := {|
  nvar := 0;
  nun := 0;
  nbin := 0;
|}.

Definition Fresh := State Names.

Definition gensym_var (tt : unit) : Fresh nat :=
  fun n => ({| nvar := S (nvar n); nun := nun n; nbin := nbin n |}, nvar n).

Definition gensym_un (tt : unit) : Fresh nat :=
  fun n => ({| nvar := nvar n; nun := S (nun n); nbin := nbin n |}, nun n).

Definition gensym_bin (tt : unit) : Fresh nat :=
  fun n => ({| nvar := nvar n; nun := nun n; nbin := S (nbin n) |}, nbin n).

End Context.

#[local] Instance fresh_has_map (St : Type) : HasMap (State St) :=
  @fresh_map St.

#[local] Instance fresh_has_pure (St : Type) : HasPure (State St) :=
  @fresh_pure St.

#[local] Instance fresh_has_bind (St : Type) : HasBind (State St) :=
  @fresh_bind St.

Section Context.

Context (X : Type).

Fixpoint label (t : term) : Fresh term :=
  match t with
  | var _ =>
    gensym_var tt >>= fun n =>
    pure (var n)
  | un n x =>
    gensym_un tt >>= fun n =>
    label x >>= fun x =>
    pure (un n x)
  | bin n x y =>
    gensym_bin tt >>= fun n =>
    label x >>= fun x =>
    label y >>= fun y =>
    pure (bin n x y)
  | rel x y =>
    label x >>= fun x =>
    label y >>= fun y =>
    pure (rel x y)
  end.

Definition relabel (t : term) : term := run (label t) no_names.

End Context.

Compute map relabel (gen 0).
Compute map relabel (gen 1).
Compute map relabel (gen 2).

Section Context.

Import IndexedTermNotations.

Compute map relabel (gen_all 0).
Compute map relabel (gen_all 1).
Compute map relabel (gen_all 2).

End Context.
