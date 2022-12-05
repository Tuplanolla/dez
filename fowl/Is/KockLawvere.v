From DEZ.Is Require Export
  Ring Isomorphic.
From DEZ.Supports Require Import
  EquivalenceNotations ArithmeticNotations.

(** This is a literal translation from topos theory,
    so it may not make any sense in Coq as stated,
    because [X] is a setoid relation and [Prop] is a thing. *)

Section Context.

Context (A : Type) (X : A -> A -> Prop)
  (x : A) (f : A -> A) (k : A -> A -> A) (y : A) (m : A -> A -> A)
  `{!IsRing X x f k y m}.

#[local] Instance ring_has_equiv_rel : HasEquivRel A := X.
#[local] Instance ring_has_zero : HasZero A := x.
#[local] Instance ring_has_neg : HasNeg A := f.
#[local] Instance ring_has_add : HasAdd A := k.
#[local] Instance ring_has_one : HasOne A := y.
#[local] Instance ring_has_mul : HasMul A := m.

Equations prod_X (a b : A * A) : Prop :=
  prod_X (x, y) (z, w) := X x z /\ X y w.

Equations fun_X (a b : {v : A | v * v == 0} -> A) : Prop :=
  fun_X g h := forall a : {v : A | v * v == 0}, X (g a) (h a).

Equations kl (z w : A) (a : {v : A | v * v == 0}) : A :=
  kl z w (v; _) := z + v * w.

(** ** Kock--Lawvere Axiom *)

Class IsKL : Type := {
  kl_is_ring :> IsRing X x f k y m;
  kl_is_iso :> IsBiInv prod_X fun_X (prod_uncurry kl);
}.

End Context.
