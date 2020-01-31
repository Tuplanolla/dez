# Scattered Notes

Do these things.

* Imagine a hub, where roosters, camels and sea thrifts grow.
* Set up build automation; see diagram `habitat.dot`.
* Add adverb subdirectories to arrange different conceps with similar names.
  Read literature on "many-sorted" or "multi-sorted"
  "equational logic" or "universal algebra".
* Regular semigroups have two equivalent definitions;
  try to implement them as an isomorphism.
* Integrate Thrift into the mess.
* Monoidal categories now.

Some rules.

* Abbreviate
    * Coq has: refl, sym, trans, assoc, comm, involutive,
      distr (binary-binary distributive),
      l (left), r (right), inj (functionally injective),
      reg (operationally regular), cancel (operationally cancellative),
      distr, swap, comm, extrusion,
      extrusion (heterogeneous associativity)
    * Coq reserves: fun, unit
    * Categorical literature has: Mag, Mon, Grp, Top, op
* Import
    * Coq has: refl, sym, trans, assoc, comm, distr,
      l (left), r (right), inj (injective)
    * Maniunfold has: fn (function), un (unit), unl (unital), invol, absorb

Wikipedia has the following wild conjecture.
It is not mentioned in literature, but appears to be very useful.
Perhaps there is other terminology in many-sorted universal algebra.
Investigate.

* f : Q × R → S (binary function)
    Example: exponentiation
    Example: set membership
    Examples: matrix multiplication, the tensor product, and the Cartesian product
* f : R × R → S (internal binary function)
    Example: internal binary relations
    Examples: the dot product, the inner product, and metrics
* f : R × S → S (external binary operation)
    Examples: dynamical system flows, group actions, projection maps, and scalar multiplication
* f : S × S → S (binary operation)
    Examples: addition, multiplication, permutations, and the cross product

There are some most general types for various unification problems
in `garbage/Unification.v`.

```
% This is the first known publication of the broker pattern.
% Surprisingly, the broker revisited pattern by the same authors ruin it all.

@book{buschmann-1996,
  author = {Frank Buschmann and Regine Meunier and Hans Rohnert and
    Peter Sommerlad and Michael Stal},
  title = {Pattern-Oriented Software Architecture},
  subtitle = {A System of Patterns},
  chapter = {Architectural Patterns / Distributed Systems / Broker},
  date = {1996},
  edition = {1},
  volume = {1},
  pages = {99--122},
  publisher = {John Wiley \& Sons},
}
```

```
From Maniunfold.Has Require Export
  EquivalenceRelation BinaryOperation Unit UnaryOperation.
From Maniunfold.Is Require Export
  Proper Monoid ExternallyInvertible.
From Maniunfold.ShouldHave Require Import
  EquivalenceRelationNotations AdditiveNotations.

Class IsGrp {A : Type} {has_eq_rel : HasEqRel A}
  (has_bin_op : HasBinOp A) (has_un : HasUn A)
  (has_un_op : HasUnOp A) : Prop := {
  un_op_is_proper :> IsProper (eq_rel ==> eq_rel) un_op;
  bin_op_un_is_monoid :> IsMon bin_op un;
  (** Changing [IsInv] to [IsExtInv] here... *)
  bin_op_un_un_op_is_invertible :> IsExtInv bin_op un un_op;
}.

Section Context.

Context {A : Type} `{is_grp : IsGrp A}.

Theorem un_op_absorb : - 0 == 0.
Proof.
  rewrite <- (r_un (- 0)).
  (** ...works here... *)
  rewrite (l_ext_inv 0).
  reflexivity. Qed.

Theorem bin_op_l_inj : forall x y z : A,
  z + x == z + y -> x == y.
Proof.
  intros x y z p.
  rewrite <- (l_un x).
  (** ...but breaks right here. *)
  rewrite <- (l_ext_inv z).
  rewrite <- (assoc (- z) z x).
  rewrite p.
  rewrite (assoc (- z) z y).
  rewrite (l_ext_inv z).
  rewrite (l_un y).
  reflexivity. Qed.
```
