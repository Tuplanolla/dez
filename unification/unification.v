From Coq Require Import List.

Import ListNotations.

(** Is this Herbrandization? *)

Set Implicit Arguments.
Set Maximal Implicit Insertion.

#[local] Open Scope bool_scope.

Inductive term : bool -> Set :=
  | var (n : nat) : term false
  | un (n : nat) (x : term false) : term false
  | bin (n : nat) (x y : term false) : term false
  | rel (x y : term false) : term true.

Fail Scheme Equality for term.

Fixpoint eqb (b c : bool) (x : term b) (y : term c) : bool :=
  match x, y with
  | var n, var p => Nat.eqb n p
  | un n x, un p y => Nat.eqb n p && eqb x y
  | bin n x y, bin p z w => Nat.eqb n p && eqb x z && eqb y w
  | rel x y, rel z w => eqb x z && eqb y w
  | _, _ => false
  end.

Compute rel (bin 0 (var 0) (var 1)) (var 0).

Fixpoint occurs (n : nat) (b : bool) (x : term b) : bool :=
  match x with
  | var p => Nat.eqb n p
  | un _ x => occurs n x
  | bin _ x y => occurs n x || occurs n y
  | rel x y => occurs n x || occurs n y
  end.

Fixpoint subb (b c : bool) (x : term b) (y : term c) : bool :=
  eqb x y ||
  match x, y with
  | var _, rel _ _ => false
  | var n, y => negb (occurs n y)
  | un n x, un p y => Nat.eqb n p && subb x y
  | bin n x y, bin p z w => Nat.eqb n p && subb x z && subb y w
  | rel x y, rel z w => subb x z && subb y w
  | _, _ => false
  end.

Definition sub (b c : bool) (x : term b) (y : term c) : Prop :=
  is_true (subb x y).

Compute subb
  (var 0)
  (rel (var 2) (var 0)).

Compute subb
  (rel (var 2) (var 0))
  (rel (bin 0 (var 0) (var 1)) (var 0)).

Compute subb
  (rel (var 1) (var 0))
  (rel (bin 0 (var 0) (var 1)) (var 0)).

(** List monad goes here. *)

Definition pure (A : Type) (x : A) : list A :=
  [x].

Fixpoint join (A : Type) (x : list (list A)) : list A :=
  match x with
  | [] => []
  | a :: y => a ++ join y
  end.

Definition bind (A B : Type) (f : A -> list B) (x : list A) : list B :=
  join (map f x).

Notation "x '>>=' f" := (bind f x) (at level 20).

Fail Fail Notation "'do' a '<-' x ';' b" := (bind (fun a : _ => b) x)
  (at level 200, a name, x at level 100, b at level 200).

Module IndexedTermNotations.

Notation "'x_' n" := (var n)
  (at level 0, n at level 100, format "'x_' n", only printing).
Notation "'-_' n x" := (un n x)
  (at level 50, format "-_ n  x", only printing).
Notation "x '+_' n y" := (bin n x y)
  (at level 50, format "x  +_ n  y", only printing).

End IndexedTermNotations.

Module TermNotations.

Notation "'x'" := (var _)
  (at level 0, format "'x'", only printing).
Notation "'-'' x" := (un _ x)
  (at level 50, format "-'  x", only printing).
Notation "x '+'' y" := (bin _ x y)
  (at level 50, format "x  +'  y", only printing).

End TermNotations.

(** Generate all trees of depth less than [m], using only one variable. *)

Fixpoint gen (m : nat) : list (term false) :=
  match m with
  | O => pure (var 0)
  | S m' =>
    gen m' >>= fun y =>
    [un 0 y] ++ (gen m' >>= fun z =>
    [bin 0 y z])
  end.

Compute gen 0.
Compute gen 1.
Compute gen 2.

Section Context.

Import TermNotations.

Compute join (map gen (seq 0 1)).
Compute join (map gen (seq 0 2)).
Compute join (map gen (seq 0 3)).

End Context.

(** Generate all trees of depth less than [m], using more variables. *)

Fixpoint gen' (m : nat) : list (term false) :=
  match m with
  | O => pure (var m)
  | S m' =>
    gen' m' >>= fun y =>
    [un m y] ++ (gen' m' >>= fun z =>
    [bin m y z])
  end.

(*

`(R (k x y) x) = rel (bin 0 (var 0) (var 1)) (var 0) : term true
`(R z x) <= `(R (k x y) x) : bool

x <- f x'
x <- k x' x''
y <- g y'
y <- m y' y''
R x y

*)
