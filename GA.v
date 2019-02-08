Require Import ZArith.

Open Scope Z_scope.

Inductive dtree (A : Type) : nat -> Type :=
  | dleaf : A -> dtree A O
  | dbranch : forall n, dtree A n -> dtree A n -> dtree A (S n).

Arguments dleaf {A} x.
Arguments dbranch {A} {n} l r.

Check dbranch (dbranch (dleaf 42) (dleaf 13)) (dbranch (dleaf 7) (dleaf 20)).

Inductive stree (A : Type) : nat -> Type :=
  | sleaf : A -> stree A O
  | sbranch : forall n m, stree A n -> stree A m -> stree A (S (max n m)).

Arguments sleaf {A} x.
Arguments sbranch {A} {n m} l r.

Check sbranch (sbranch (sleaf 42) (sleaf 13)) (sleaf 7).

(** This is a balanced binary tree with elements only in the leaves. *)
Inductive tree (A : Type) : nat -> Type :=
  | leaf : A -> tree A O
  | branch : forall n, tree A n -> tree A n -> tree A (S n).

Arguments leaf {A} x.
Arguments branch {A} {n} l r.

Check leaf 42.
Check branch (leaf 42) (leaf 13).
Check branch (branch (leaf 42) (leaf 13)) (branch (leaf 7) (leaf 20)).
Fail Check branch (leaf 42) (branch (leaf 7) (leaf 20)).

Definition lx {A : Type} (t : tree A O) : A :=
  match t with
  | leaf x => x
  end.

Definition bl {A : Type} {n : nat} (t : tree A (S n)) : tree A n :=
  match t with
  | branch l _ => l
  end.

Definition br {A : Type} {n : nat} (t : tree A (S n)) : tree A n :=
  match t with
  | branch _ r => r
  end.

Fixpoint map {A B : Type} (f : A -> B)
  {n : nat} (t : tree A n) : tree B n :=
  match t with
  | leaf x => leaf (f x)
  | branch l r => branch (map f l) (map f r)
  end.

(** This is called the _convoy pattern_. *)
Fixpoint zip' {A1 A2 B : Type} (f : A1 -> A2 -> B)
  {n : nat} (t1 : tree A1 n) (t2 : tree A2 n) : tree B n :=
  match t1 in tree _ n return tree A2 n -> tree B n with
  | leaf x1 => fun t2 => leaf (f x1 (lx t2))
  | branch l1 r1 => fun t2 => branch (zip' f l1 (bl t2)) (zip' f r1 (br t2))
  end t2.

(** This is a second-order convoy. *)
Fixpoint zip {A1 A2 B : Type} (f : A1 -> A2 -> B)
  {n : nat} (t1 : tree A1 n) (t2 : tree A2 n) : tree B n :=
  match n return tree A1 n -> tree A2 n -> tree B n with
  | O => fun t1 t2 => leaf (f (lx t1) (lx t2))
  | S _ => fun t1 t2 => branch (zip f (bl t1) (bl t2)) (zip f (br t1) (br t2))
  end t1 t2.

Compute zip Zplus (leaf 42) (leaf 13).
Compute zip Zplus (branch (leaf 42) (leaf 13)) (branch (leaf 7) (leaf 20)).
Fail Compute zip Zplus (leaf 42) (branch (leaf 7) (leaf 20)).

Notation "x + y" := (zip Zplus x y).
Notation "x * y" := (map (Zmult x) y).

(* ~ x = x
   ~ (l, r) = (~ l, - (~ r)) *)
Fixpoint aux {A : Type} (fneg : A -> A)
  {n : nat} (t : tree A n) : tree A n :=
  match t with
  | leaf x => leaf x
  | branch l r => branch (aux fneg l) (map fneg (aux fneg r))
  end.

Notation "~ x" := (aux Zopp x).

Compute aux Zopp (branch (branch (leaf 42) (leaf 13)) (branch (leaf 7) (leaf 20))).

(* x1 /\ x2 = x1 * x2
   (l1, r1) /\ (l2, r2) = (l1 /\ l2, r1 /\ l2 + l1 /\ r2) *)
(** We must run the convoy in reverse here. *)
Fixpoint outer {A : Type} (fadd fmul : A -> A -> A) (fneg : A -> A)
  {n : nat} (t1 : tree A n) (t2 : tree A n) : tree A n :=
  match t2 in tree _ n return tree A n -> tree A n with
  | leaf x2 => fun t1 => leaf (fmul (lx t1) x2)
  | branch l2 r2 => fun t1 => branch
    (outer fadd fmul fneg (bl t1) l2) (zip fadd
    (outer fadd fmul fneg (br t1) l2)
    (outer fadd fmul fneg (aux fneg (bl t1)) r2))
  end t1.

Notation "x /\ y" := (outer Zplus Zmult Zopp x y).

(* x1 ** x2 = x1 * x2
   (l1, r1) ** (l2, r2) = (l1 ** l2) + (r1 ** (~ r2)) *)
Fixpoint inner {A : Type} (fadd fmul : A -> A -> A) (fneg : A -> A)
  {n : nat} (t1 : tree A n) (t2 : tree A n) : A :=
  match t1 in tree _ n return tree A n -> A with
  | leaf x1 => fun t2 => fmul x1 (lx t2)
  | branch l1 r1 => fun t2 => fadd
    (inner fadd fmul fneg l1 (bl t2))
    (* metric signature here *) (inner fadd fmul fneg r1 (aux fneg (br t2)))
  end t2.

Notation "x '.*' y" := (inner Zplus Zmult Zopp x y) (at level 42).

Compute inner Zplus Zmult Zopp
  (branch (branch (leaf 42) (leaf 13)) (branch (leaf 7) (leaf 69)))
  (branch (branch (leaf 42) (leaf 13)) (branch (leaf 7) (leaf (Zopp 69)))).

(* Fixpoint flapr {A : Type} (f : forall n, tree A n -> tree A n)
  {n : nat} (t : tree A n) : tree A n :=
  match t with
  | leaf x => leaf x
  | branch l r => branch (flapr f l) (flapr f (f _ r))
  end. *)
Fixpoint flapr {A : Type} (f : forall n, tree A n -> tree A n)
  {n : nat} (t : tree A n) : tree A n :=
  match n in nat return tree A n -> tree A n with
  | O => fun t => leaf (lx t)
  | S n => fun t => branch (flapr f (bl t)) (flapr f (f _ (br t)))
  end t.

(* >< x = x
   >< (l, r) = (>< l, >< (~ r)) *)
Fixpoint rev {A : Type} (fneg : A -> A)
  {n : nat} (t : tree A n) : tree A n :=
  match n in nat return tree A n -> tree A n with
  | O => fun t => leaf (lx t)
  | S n => fun t => branch (rev fneg (bl t)) (rev fneg (aux fneg (br t)))
  end t.

Notation ">< x" := (flapr (aux Zopp) x) (at level 13).

Compute let x := branch (branch (leaf 42) (leaf 13)) (branch (leaf 7) (leaf 69)) in
  inner Zplus Zmult Zopp x (rev Zopp x).

Fixpoint const {A : Type} (z : A)
  {n : nat} : tree A n :=
  match n with
  | O => leaf z
  | S _ => let b := const z in branch b b
  end.

Compute @const _ 0 2.

Definition inject1 {A : Type} (z : A)
  {n : nat} (t : tree A n) : tree A (S n) :=
  branch t (const z).

Fixpoint inject {A : Type} (z : A)
  {n m : nat} (t : tree A n) : tree A (m + n) :=
  match m in nat return tree A n -> tree A (m + n) with
  | O => fun t => t
  | S _ => fun t => branch (inject z t) (inject z (const z))
  end t.

Compute @inject _ 0 _ 2 (branch (leaf 42) (leaf 13)).

(* This is just [bl]. *)
Definition project1 {A : Type}
  {n : nat} (t : tree A (S n)) : tree A n :=
  match t with
  | branch l r => l
  end.

Fixpoint project {A : Type}
  {n m : nat} (t : tree A (m + n)) : tree A n :=
  match m in nat return tree A (m + n) -> tree A n with
  | O => fun t => t
  | S k => fun t => project (bl t)
  end t.

Compute @project _ _ 1 (branch (branch (leaf 42) (leaf 13)) (branch (leaf 7) (leaf 69))).

(* Now define the free algebra and compute specializations. *)

Inductive free (A : Type) (z : A) : Type :=
  | f_lift : A -> free A z
  | f_add : free A z -> free A z -> free A z
  | f_neg : free A z -> free A z
  | f_mul : free A z -> free A z -> free A z.

Arguments f_lift {A} {z} x.
Arguments f_add {A} {z} x y.
Arguments f_neg {A} {z} x.
Arguments f_mul {A} {z} x y.

Check (@f_lift Z 0 42).

Notation "x + y" := (f_add x y).
Notation "- x" := (f_neg x).
Notation "x * y" := (f_mul x y).

Require Import String.

Open Scope string_scope.

Check (@f_lift string "0" "x").
Compute (f_mul (f_lift "x") (f_add (f_lift "y") (f_lift "0")) : free string "0").

(* Structural equality. *)
Fixpoint f_eq {A : Type} (eq : A -> A -> bool)
  {z : A} (a1 a2 : free A z) : bool :=
  match a1, a2 with
  | f_lift x1, f_lift x2 => eq x1 x2
  | f_add x1 y1, f_add x2 y2 => f_eq eq x1 x2 && f_eq eq y1 y2
  | f_neg x1, f_neg x2 => f_eq eq x1 x2
  | f_mul x1 y1, f_mul x2 y2 => f_eq eq x1 x2 && f_eq eq y1 y2
  | _, _ => false
  end.

(* This is weak. *)
Fixpoint simpl {A : Type} {z : A}
  (eq : A -> A -> bool) (a : free A z) : free A z :=
  match a with
  | f_lift x => f_lift x
  | f_add x y => if f_eq eq (f_lift z) x then simpl eq y else
    if f_eq eq (f_lift z) y then simpl eq x else
    f_add (simpl eq x) (simpl eq y)
  | f_neg x => f_neg (simpl eq x)
  | f_mul x y => if f_eq eq (f_lift z) x then f_lift z else
    if f_eq eq (f_lift z) y then f_lift z else
    f_add (simpl eq x) (simpl eq y)
  end.

Definition string_eq (s1 s2 : string) : bool :=
  if string_dec s1 s2 then true else false.

Compute simpl string_eq
  (f_mul (f_lift "x") (f_add (f_lift "y") (f_lift "0")) : free string "0").

Compute outer f_add f_mul f_neg
  (branch (leaf (f_lift "a")) (leaf (f_lift "x")))
  (branch (leaf (f_lift "b")) (leaf (f_lift "y"))) : tree (free string "0") 1.
