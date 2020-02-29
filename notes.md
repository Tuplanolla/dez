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
* Now that we have one-sorted algebra (abstract algebra)
  generalized to many-sorted algebra (universal algebra) and
  oidified to one-sorted partial algebra (category theory),
  what happens if we go looking for many-sorted partial algebra?
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
* Order
    * Most common properties first
      (such as `eq_rel` before `bin_op` before `un`).
    * Structural members explicitly dealing with operations in
      lexicographical order (such as `eq_rel_is_eq` before `bin_op_is_proper`).
* Implicit
    * Do not make operational class inferrable parameters implicit,
      because unexpected maximal insertion breaks everything (pages of errors).

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

After investigation, we can conclude that, indeed,
universal algebra does not talk about external things.
It leaves such matters to two-sorted equational theories.
Semigroup actions provide another view on this.
The Haskell package `acts` concisely states the following properties.

```
a <<* (b <<* x) = (a <> b) <<* x
(y <<- x) <<* x = y
(z <<- y) <> (y <<- x) = z <<- x
(-<>) = flip (<<-)
(y -<> z) <> (x -<> y) = x -<> z

-- In prefix notation...

l_act a (l_act b x) = l_act (bin_op a b) x
l_act (l_tor y x) x = y
bin_op (l_tor z y) (l_tor y x) = l_tor z x
fl_tor x y = l_tor y x
bin_op (fl_tor y z) (fl_tor x y) = fl_tor x z

-- Now the dual construction...

(x *>> a) *>> b = x *>> (a <> b)
x *>> (x ->> y) = y
(x ->> y) <> (y ->> z) = x ->> z
(<>-) = flip (->>)
(y <>- x) <> (z <>- y) = z <>- x

r_act (r_act x a) b = r_act x (bin_op a b)
r_act x (r_tor x y) = y
bin_op (r_tor x y) (r_tor y z) = r_tor x z
fr_tor x y = r_tor y x
bin_op (fr_tor y x) (fr_tor z y) = fr_tor z x

-- Now the questions are...

-- When does l_act equal flip r_act?
-- Precisely when bin_op is commutative and l_act is right-cancellative,
-- that is,
l_act (bin_op a b) x = l_act (bin_op b a) x -- implies
bin_op a b = bin_op b a -- and then commutativity finishes it up.
-- More generally, right-cancellativity says that...
l_act x z = l_act y z -> x = y
-- This is a generalization of a basic result from module theory
-- (the module case is easier, because the underlying group having an inverse
-- gives cancellation for free).

-- When does fl_tor equal r_tor and fr_tor equal l_tor and
-- is there a Galois connection involved?

-- Suppose bin_op is commutative and thus the actions coincide.
-- By alpha-renaming and setoid rewriting...

l_act (l_tor y x) x = l_act (r_tor x y) x -- Combine the first two
-- action equations by transitivity.
l_tor y x = r_tor x y -- Apply cancellation of actions
-- (this requires right-cancellativity again).
flip r_tor y x = l_tor y x -- Flip and symmetrize.
-- The same works for the dual construction.

-- For group actions,
-- literature tells us that l_act and r_act are compatible if
-- g <<* p = p *>> g ^-1 or l_act g p = r_act p (g ^-1).
-- If the group satisfies g ^-1 = g,
-- then l_act and r_act coincide,
-- as is the case with commutative and cancellative actions,
-- but this is condition is stronger!
```

The Scala library `spire` only defines torsors over abelian group actions,
requiring both left and right actions to coincide.

> A (left) semigroup/monoid/group action of G on P is simply the implementation of a method actl(g, p), or g |+|> p, such that:
> 1. (g |+| h) |+|> p === g |+|> (h |+|> p) for all g, h in G and p in P.
> 2. id |+|> p === p for all p in P (if id is defined)
>
> A (right) semigroup/monoid/group action of G on P is simply the implementation of a method actr(p, g), or p <|+| g, such that:
> 1. p <|+| (g |+| h) === (p <|+| g) <|+| h for all g, h in G and p in P.
> 2. p <|+| id === p for all p in P (if id is defined)
>
> A semigroup/monoid/group action of G on P is the combination of compatible left and right actions, providing:
>     the implementation of a method actl(g, p), or g |+|> p, such that:
> 1. (g |+| h) |+|> p === g |+|> (h |+|> p) for all g, h in G and p in P.
> 2. id |+|> p === p for all p in P (if id is defined)
>     the implementation of a method actr(p, g), or p <|+| g, such that:
> 3. p <|+| (g |+| h) === (p <|+| g) <|+| h for all g, h in G and p in P.
> 4. p <|+| id === p for all p in P (if id is defined)
> In addition, if G is a group, left and right actions are compatible:
> 5. g |+|> p === p <|+| g.inverse.
>
> A Torsor[V, R] requires an AbGroup[R] and provides Action[V, R], plus a diff operator, <-> in additive notation, such that:
> 1. (g <-> g) === scalar.id for all g in G.
> 2. (g <-> h) +> h === g for all g, h in G.
> 3. (g <-> h) +> i === (i <-> h) +> g for all g, h in G.
> 4. (g <-> h) === -(h <-> g) for all g, h in G.

This makes sense, but is a bit too specific.

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
