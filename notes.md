# Notes

The purpose of these informal notes is
to remind the writer of their own stupidity.
There are many conventions that need to be followed,
because otherwise things break in surprising ways.

## Personal Notes by Sampsa Kiiskinen

### Build Automation

Run `make` inside `bird` to build it with Make.
Eventually running `make` at the root will work too.
Even more eventually `dune` might work as well.

### Coherence Conditions

When defining operational classes or their instances,
they must be marked transparent,
for classes with `Typeclasses Transparent` or, for instances, with `Defined`.
When defining instances of predicative classes,
they must be marked opaque, usually with `Qed`.

When defining predicative classes,
all the operational classes must be constraints,
all the predicative classes should be instance fields and
all the other things, including propositions should be ordinary fields.

Predicative classes with propositions as fields
should be single-field if possible.
Predicative classes with instance fields must not be single-field.

### Implicit Generalization

When defining classes, implicit generalization must not be used.
When writing definitions or proving theorems,
implicit generalization should be used in the `Context` of a `Section`,
which itself is usually named `Context`.

### Imports and Exports

When defining operational classes,
all the constraining operational classes must be exported,
in the order they are used.

When defining predicative classes,
all the constraining operational classes and
constituent predicate classes must be exported,
in the order they are used.
Superclasses, when constructed separately, such as `IsIdem` for a `Group`,
must also be exported, in the order they are used.

If nothing else is exported from `Maniunfold`, always export `Init`.

Favor exporting in the form
`From Maniunfold.Is Require Export OneSortedly.Magma OneSortedly.Unital`,
where the placement in the main hierarchy is at the top.

### Naming Conventions

Operative classes are prefixed with `Has` and predicative classes with `Is`.
Abbreviations shorter than six characters are favored, whenever possible.

Fields are prefixed with the nouns and then the verb.
For example, we would have `bin_op_un_is_mon :> IsMon bin_op un`.

Instance fields contain the verb `is`, while plain fields do not.
For example, we would have `bin_op_is_assoc :> IsAssoc bin_op` and
`bin_op_assoc : forall x y z : A, x + (y + z) = (x + y) + z`.

### Class Duality

When defining things in `Offers`,
use a context with only `Has` things in it,
without implicit generalization.

When defining things in `Provides`,
use a context with only `Is` things in it,
with implicit generalization.

### Name Playground

Derived operations and theorems need not be prefixed,
although some prefix options are the modal verbs `Can`, `Could`,
`May`, `Might`, `Must`, `Ought`, `Shall`, `Should`, `Will` and `Would` and
the other verbs

* `Advises`, `Affirms`, `Affords`, `Allows`, `Articulates`,
  `Asserts`, `Assigns`, `Assumes`, `Attests`,
* `Backs`, `Builds`,
* `Certifies`, `Confirms`, `Conveys`, `Creates`, `Cultivates`,
* `Declares`, `Defends`, `Defines`, `Delivers`,
  `Demonstrates`, `Depicts`, `Describes`, `Designates`,
  `Determines`, `Discerns`, `Displays`, `Distills`, `Distinguishes`,
* `Embodies`, `Endorses`, `Entails`, `Establishes`,
  `Evidences`, `Evinces`, `Exhibits`, `Exposes`, `Expresses`,
* `Figures`, `Fixes`, `Fosters`, `Fulfills`,
* `Gives`, `Goes`, `Grants`,
* (`Has`), `Holds`,
* `Implies`, `Incites`, `Indicates`, `Informs`, `Instigates`, (`Is`),
* `Justifies`,
* `Lets`,
* `Maintains`, `Makes`, `Manifests`, `Means`, `Mentions`,
* `Necessitates`, `Needs`,
* `Obeys`, `Offers`,
* `Permits`, `Points`, `Poses`, `Posits`,
  `Postulates`, `Presents`, `Preserves`, `Presumes`, `Produces`, `Proposes`,
* `Qualifies`, `Quantifies`,
* `Raises`, `Reasserts`, `Recites`, `Reckons`,
  `Recognizes`, `Records`, `Refers`, `Refines`,
  `Reflects`, `Represents`, `Resolves`,
* `Sanctions`, `Satisfies`, `Says`, `Serves`,
  `Shows`, `Solves`, `Specifies`, `Speculates`,
  `States`, `Stipulates`, `Suggests`, `Supplies`,
  `Supports`, `Supposes`, `Sustains`,
* `Tells`, `Thinks`,
* `Upholds`,
* `Works` and perhaps even `Was`,
* `Yields`.

### Compatibility

The standard library in version 8.11.0
has the follwing classes we want to be compatible with.

* `DecidableClass`
    * `Decidable`
* `EquivDec`
    * `DecidableEquivalence`
    * `EqDec`
* `Init`
    * `Unconvertible`
* `Morphisms`
    * `Proper`
    * `ProperProxy`
    * `PartialApplication`
    * `Params`
    * `Normalizes`
* `RelationClasses`
    * `IsRefl -> Reflexive`
    * `IsIrrefl -> Irreflexive`
    * `IsSym -> Symmetric`
    * `IsAsym -> Asymmetric`
    * `IsTrans -> Transitive`
    * `IsPreord -> PreOrder`
    * `IsStrPartOrd -> StrictOrder`
    * `IsPartEq -> PER`
    * `IsEq -> Equivalence`
    * `IsAntisym -> Antisymmetric`
    * `subrelation`
    * `RewriteRelation`
    * `IsPartOrd -> PartialOrder`
* `RelationPairs`
    * `Measure`
* `SetoidClass`
    * `Setoid`
    * `PartialSetoid`
* `SetoidDec`
    * `DecidableSetoid`
    * `EqDec`
* `SetoidTactics`
    * `DefaultRelation`

### Subclass Specialization

With the `coq-ltac-iter` plugin, we could do the following,
although this approach might be overkill.

```
Create HintDb group.

Hint Extern 1 => change bin_op with add : group.
Hint Extern 1 => change un with zero : group.
Hint Extern 1 => change un_op with neg : group.

Ltac change_group := let k x := x in foreach [db : group] k.
```

None of these issues prevent working on the system,
but solving some of them would get rid of a lot of pointless busywork.

### Piles of Things to Do

It would be easier to separate algebraic, relational,
functional, order-theoretic, metric, etc properties from each other,
but, alas, they are too intertwined for such a separation to be useful.

Do these things.

* Add adverb subdirectories to arrange different conceps with similar names.
  Read literature on "many-sorted" or "multi-sorted"
  "equational logic" or "universal algebra".
* Regular semigroups have two equivalent definitions;
  try to implement them as an isomorphism.
* Set up build automation; see diagram `habitat.dot`.
* Integrate Thrift into the mess.
* Now that we have one-sorted algebra (abstract algebra)
  generalized to many-sorted algebra (universal algebra) and
  oidified to one-sorted partial algebra (category theory),
  what happens if we go looking for many-sorted partial algebra?
* Perhaps call the maps involved in an equivalence section and retraction.
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

Do not try these.

* Do not get rid of subclass hierarchies for operational classes,
  because they are needed to resolve subtypings like `HasAdd <: HasBinOp`.
* Do not get rid of `Typeclasses Transparent` for operational classes,
  because they are needed to reduce contexts like
  `A : Type, has_zero : HasZero A |- HasZero (HasNullOp A)`.

Wikipedia has the wild conjecture on "externality".
It is not mentioned in literature, but appears to be useful.
Perhaps there is other terminology in many-sorted universal algebra.
Investigate.

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

We have injectivity `- x == - y -> x == y` and
(left) cancellativity `z + x == z + y -> x == y`.

We have something `- x == x` and
something `z + x == x`.
We have unary idempotency `- - x == - x` and
something `z + z + x == z + x`.
We have involutivity `- - x == x` and
something `z + z + x == x`.
We have unary absorption `- 0 == 0` and
(right) absorption `z * 0 == 0`.
We have unary distributivity `- (x + y) == - x + - y` and
(left) distributivity `z * (x + y) == z * x + z * y`.
We have unary distributivity `- x * - y == - x * - y` and
something `z * (x + y) == z * x + z * y`.

Everything we have seen is of the following forms.

```
x
- x
- - x
x + x
- x + x
x + - x
- x + - x
- (x + x)
- (- x + x)
- (x + - x)
(x + x) + x
x + (x + x)
(x + x) + (x + x)
```

There is an exhaustive generator for all possible free terms and
equational theories in `../garbage/GroupThyGen.hs` etc.

There are some most general types for various unification problems
in `garbage/Unification.v`.

### Curious Perversions

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

```
(** It is horrifying to try to bend the setoid model to do this. *)
Class IsGrdMon {A : Type} {P : A -> Type}
  (A_has_bin_op : HasBinOp A) (A_has_un : HasUn A)
  (P_has_grd_bin_op : HasGrdBinOp P) (P_has_grd_un : HasGrdUn P) : Prop := {
  bin_op_un_is_mon :> IsMon (A := A) bin_op un;
  grd_assoc : forall (i j k : A) (x : P i) (y : P j) (z : P k),
    rew assoc i j k in (x G+ (y G+ z)) = (x G+ y) G+ z;
  grd_l_unl : forall (i : A) (x : P i),
    rew l_unl i in (G0 G+ x) = x;
  grd_r_unl : forall (i : A) (x : P i),
    rew r_unl i in (x G+ G0) = x;
}.
```

## Simple Laws about Nonprominent Properties of Binary Relations by Jochen Burghardt

Regarding common and less common binary relations,
Burghardt defines a big list of them.
Unary relations or predicates of other kinds are not discussed,
but the search term "encyclopedic" might be of use.

## Type Classes for Mathematics in Type Theory by Spitters and van der Weegen

Regarding overlapping instances of operational classes (major issue),
Spitters and van der Weegen claim that "the issue rarely arises".
This seems dubious to a Haskell programmer,
but I will trust their word and see what happens.

> Because predicate classes only provide contextual information and
> are insulated from the actual algebraic expressions,
> their instances can always be kept entirely opaque ---
> only their existence matters.
> Together, these properties largely defuse
> an argument occasionally voiced against type classes
> concerning perceived unpredictability of instance resolution.
> While it is certainly true that in contexts with redundant information
> it can become hard to predict which instance
> of a predicate class will be found by proof search,
> it simply does not matter which one is found.
> Moreover, for operational type classes the issue rarely arises because
> their instances are not nearly as abundant.

Regarding conjunctions of properties or property generators
in the definitions of predicative classes (minor issue),
Spitters and van der Weegen claim that
"almost any generic predicate worth naming
is worth representing as a predicate type class" and
use hybrid operational-style predicative classes in the implementation.
It is a bit strange not to mention the hybrid approach,
but I will follow suit and see what happens.

> We use names for properties like distributivity and absorption,
> because these are type classes as well
> (which is why we declare them with `:>`).
> It has been our experience
> that almost any generic predicate worth naming
> is worth representing as a predicate type class,
> so that its proofs will be resolved as instances
> behind the scenes whenever possible.
> Doing this consistently minimizes administrative noise in the code,
> bringing us closer to ordinary mathematical vernacular.
> Indeed, we believe that type classes are an elegant and
> apt formalization of the seemingly casual manner in which
> ordinary mathematical presentation assumes implicit administration and
> use of a 'database' of properties previously proved.
> Much more so than the existing canonical structures facility,
> because canonical structures can only be used
> with bundled representations,
> which we argued against in section 3.

Regarding modules and the expression problem (minor issue),
Spitters and van der Weegen make no claims and
fail to account for this in the implementation.
I have not found a solution to this problem either,
but disallowing operational class sharing and
using explicit operational class inheritance might work
(or exacerbate the overlapping instance problem).
I will try this and see what happens.

Regarding the scope of operational classes (minor issue),
Spitters and van der Weegen claim that
"what we really need are canonical names" and
have one module with all the operational classes in the implementation.
This conflicts with explicit operational class inheritance,
so I will ignore their advice and see what happens.

> Because `e` and `op` are freshly introduced local names,
> we cannot bind notations to them prior to this theorem.
> Hence, if we want notations,
> what we really need are canonical names for these components.
> This is easily accomplished with single-field type classes
> containing one component each,
> which we will call operational type classes.

Regarding inheritance between operational classes (major issue),
Spitters and van der Weegen make no claims,
but seem to use the concept in the implementation.
I will also make use of operational class inheritance.

Regarding the sharing of operational classes
between different structures (minor issue),
Spitters and van der Weegen make no claims,
but seem to share them as they see fit in the implementation.
Whether sharing is required by canonical names or vice versa is unclear.
I will let explicit operational class inheritance
give rise to sharing and see what happens.

Regarding conflicting or extensible notations (minor issue),
Spitters and van der Weegen make no claims and
do not support such a thing in the implementation.
However, I have found a way to accomplish this
with scopes and module shadowing.

Regarding dependently-typed operational type classes (major issue),
Spitters and van der Weegen make no claims,
but use them with implicit generalization in the implementation.
This must be too obvious to be mentioned,
even though implicit generalization generates unpredictable names
for the inferred arguments, making the code fragile.
I will try to formulate a naming convention
that produces predictable names and and see what happens.

Regarding efficiency of extracted code (major issue),
Spitters and van der Weegen make a related claim that
"efficiency of computation using type-checked terms is not affected".
I have also observed this,
but based on the assumption that the OCaml compiler
can inline identity, constant and projection functions
across modules (this is likely to be true, but not a given).

Regarding the universal usability (major issue),
Spitters and van der Weegen claim that they could make
"an unequivocal endorsement of type classes".
I have found a simple counterexample,
where trying to model higher groupoid structure is
more tedious and unpleasant than it would be with plain records.
However, I might not need to do that in practice.

> There are really only two pending concerns that keeps us
> from making an unequivocal endorsement of type classes
> as a versatile, expressive, and elegant means
> of organizing proof developments.
> The first and lesser of the two is universe polymorphism
> for definitions as described in the previous section.
> The second is instance resolution efficiency.
> In more complex parts of our development
> we are now experiencing increasingly serious efficiency problems,
> despite having already made sacrifices
> by artificially inhibiting many natural class instances
> in order not to further strain instance resolution.
> Fortunately, there is plenty of potential for improvement
> of the current instance resolution implementation.
> One source is the vast literature
> on efficient implementation of Prolog-style resolution,
> which the hint-based proof search used
> for instance resolution greatly resembles.
> We emphasize that these efficiency problems only affect type checking;
> efficiency of computation using type-checked terms is not affected.

Regarding rewriting with lemmas that are
more general than the goal (minor issue),
Spitters and van der Weegen make no claims,
but sometimes leave operational classes out of
the definitions of predicative classes to facilitate rewriting.
Alas, this makes the use of associated notations impossible.
