# Notes

The purpose of these informal notes is
to remind the writer of their own stupidity.
There are many conventions that need to be followed,
because otherwise things break in surprising ways.

## Personal Notes by Sampsa Kiiskinen

### Build Automation

There are two build systems: GNU Make and Dune.
The system based on Make is decently good.

```
$ make -j $(nproc)
$ make run
```

The system based on Dune should work better for the OCaml components,
but is otherwise too simple to handle the build.

```
$ dune build
$ dune exec -- coqide -Q _build/default/bird DEZ fowl/Provides/PolynomialTheorems.v
```

I should probably list the dependencies and
some installation and usage instructions here as well.

### Rework the Following Sections

New experience suggests to do things a little differently.

When defining contexts,
always mark types explicit and type classes implicit.
If type classes are operational,
give the variables explicit names.
If type classes are predicative,
do not give the variables explicit names,
but do use `!` to give the classes explicit arguments.
When providing explicit arguments to type classes,
always refer to operational classes by their most specific name.
If implicit arguments are inferred incorrectly,
fix them with `Arguments` after the context ends.

Prefer `export`ing instances instead of marking them `local`;
if there are potential cycles or conflicts,
hide coherent alternatives in modules.

Take note of this distinction for operational classes.

```
Class HasIdHom (A : Type) {X : HasHom A} : Type :=
  id_hom (x : A) : x --> x.

Class HasIdHom' (A : Type) (X : A -> A -> Prop) : Type :=
  id_hom' (x : A) : X x x.
```

Naming conventions for instances go like this.

```
Instance X_has_Y {x : HasX A} : HasY A.
Instance Y_has_X {y : HasY A} : HasX A.

Instance X_Y {x : HasX A} : Y.
Instance Y_has_X {y : Y} : HasX A.

Instance X_has_Y {x : X} : HasY A.
Instance Y_X {y : HasY A} : X.

Instance X_has_Y_G {x : HasX A} : HasY (G A).
Instance Y_G_has_X {y : HasY (G A)} : HasX A.

Instance X_F_has_Y {x : HasX (F A)} : HasY A.
Instance Y_has_X_F {y : HasY A} : HasX (F A).

Instance F_has_Y (a : F A) : HasY A.
Instance has_X_F : HasX (F A).

Definition X_G {x : HasX A} : G A.
Definition Y_G {y : HasY (G A)} : A.
```

Order fields of classes first by parameters they mention and then arity.

```
Class IsNotPartOrd (A : Type) (X Y : A -> A -> Prop) : Prop := {
  part_ord_is_equiv :> IsEquiv X; (** [X] is mentioned *)
  part_ord_is_refl :> IsRefl Y; (** [Y] is mentioned at arity [1] *)
  part_ord_is_trans :> IsTrans Y; (** [Y] is mentioned at arity [3] *)
  part_ord_is_antisym :> IsAntisym X Y; (** [X] and [Y] are both mentioned *)
}.
```

### Checklist

Think you are done working on a module?
Think again!

* Check imports.
    * Check import redundancy.
    * Check import order.
    * Check import reexporting.
* Check locality annotations.
    * Check mere `typeclasses eauto` instances are local.
    * Check cyclic instances are local.
* Check names of fields.
    * Check prefix.
    * Check suffix.
* Check names of instances.
    * Check prefix.
    * Check suffix.
* Check context variables.
    * Check there are no redundant assumptions.
    * Check assumptions are not too widely scoped.
* Check syntax.
    * Check indentation.
    * Check double spacing.
    * Check final line break.

### Coherence Conditions

When defining operational classes or their instances,
they must be marked transparent,
for classes with `Typeclasses Transparent` or, for instances, with `Defined`.
When defining instances of predicative classes,
they must be marked opaque, usually with `Qed`.
Replacing operational notations requires `setoid_rewrite` instead of `rewrite`
to enable unification that goes deeper.

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
When the classes to generalize are operational,
make them explicit (possibly automatically implicit);
when the classes to generalize are predicative,
make them implicit (explicitly so).

Instances inside sections should always be marked `Global` or `Local`,
never implicitly local.

When defining multi-sorted classes,
always supply implicit type arguments explicitly,
because tracking down degeneration bugs is really annoying.

### Definitions

Prefer writing arguments to the left of `:` in definitions,
because then we do not have to `intros` variables introduced
by implicit generalization, which is fragile.

Rewrite rules true by reduction can be stated as `Fact`s.

When writing `Fixpoint` definitions,
make sure to pass recursive arguments explicitly.
Otherwise, changes in implicit argument inference will break them.

### Notations

Always provide full sections, in Agda style.
They have to come before fully applied versions,
so that full applications are preferred for printing.

Eta reduce nonkeyword notations as much as possible,
because it is annoying to have to fully apply them for type checking.
Also, no notation chains please.

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

If nothing else is exported from `DEZ`, always export `Init`.

Favor exporting in the form
`From DEZ.Is Require Export OneSortedly.Magma OneSortedly.Unital`,
where the placement in the main hierarchy is at the top.

If you export non-notation modules from notation modules,
the scope stack will be broken and life will be suffering.

### Naming Conventions

Operative classes are prefixed with `Has` and predicative classes with `Is`.
Abbreviations shorter than six characters are favored, whenever possible.

Instance fields contain the verb `is`, while plain fields do not.
For example, we would have `bin_op_is_assoc :> IsAssoc bin_op` and
`bin_op_assoc : forall x y z : A, x + (y + z) = (x + y) + z`.

We avoid using

* `O`, because it looks like zero,
* `o`, because it is used for function composition,
* `I`, because it looks like one and is used for the interval pretype,
* `i`, out of sympathy for `I` and the imaginary numbers,
* `l`, because it looks like one,
* `U`, because it looks like a type universe,
* `H`, because it is reserved by Coq for automatic names and
* `N`, `Z`, `Q` and `R`, because they are reserved by Coq for numbers.

So, following the tradition,

* types of type `Type` are named
  `A`, `B`, `C`, `D`, `E`, ...,
* type functions of type `Type -> Type` are named
  `F`, `G`, `J`, `K`, `L`, ...,
* type operators of type `Type -> Type -> Type` are named
  `K`, `L`, `M`, `P`, `S`, ...,
* type families of type `A -> Type` are named
  `P`, `S`, `T`, `V`, `W`, ...,
* higher type families of type `A -> A -> Type` are named
  `X`, `Y`, `W`, `V`, `T`, ...,
* structures of type `A` are named
  `x`, `y`, `z`, `w`, `v`, ...,
* functions of type `A -> B` are named
  `f`, `g`, `h`, `j`, `k`, ...,
* operators of type `A -> B -> C` are named
  `k`, `m`, `n`, `p`, `q`, ...,
* higher structures of type `x : A |- P x` are named
  `a`, `b`, `c`, `d`, `e`, ...,
* even higher structures of type `x : A, a : P x |- S a` are named
  `s`, `t`, `u`, `v`, `w`, ...,

although the rules should be broken with good reasons.
Here is how the names are laid out spatially.

```
a b c d e f g h j k m n p q r s t u v w x y z
|->       |->     |->         |->       |->
A B C D E F G J K L M P S T V W X Y
|->       |->   |->   |->       |->
```

It is a bit annoying how we have to shift `C` to `X`,
because otherwise the capital letters
would be so cramped to the initial segment.
However, otherwise traditions serve us just fine.

### Scopes

Should write something here.

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
    * `HasDec -> Decidable`
* `EquivDec`
    * `DecidableEquivalence`
    * `HasEquivDec -> EqDec`
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
    * `IsEquiv -> Equivalence`
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
    * `HasEquivDec -> EqDec`
* `SetoidTactics`
    * `DefaultRelation`

Another review of Coq 8.15.0 and Equations 1.2.4.

* `Classes.DecidableClass`
    * `Decidable`
* `Classes.EquivDec`
    * `DecidableEquivalence`
    * `EqDec`
* `Classes.Init`
    * `Unconvertible`
* `Classes.Morphisms`
    * `Normalizes`
    * `Params`
    * `PartialApplication`
    * `ProperProxy`
    * `Proper`
* `Classes.RelationClasses`
    * `Antisymmetric`
    * `Asymmetric`
    * `Equivalence`
    * `Irreflexive`
    * `PER`
    * `PartialOrder`
    * `PreOrder`
    * `Reflexive`
    * `RewriteRelation`
    * `StrictOrder`
    * `Symmetric`
    * `Transitive`
    * `subrelation`
* `Classes.RelationPairs`
    * `Measure`
* `Classes.SetoidClass`
    * `PartialSetoid`
    * `Setoid`
* `Classes.SetoidDec`
    * `DecidableSetoid`
    * `EqDec`
* `Classes.SetoidTactics`
    * `DefaultRelation`
* `Prop.Classes`
    * `EqDec`
    * `EqDecPoint`
    * `FunctionalElimination`
    * `FunctionalInduction`
    * `ImpossibleCall`
    * `NoConfusionPackage`
    * `NoCyclePackage`
    * `UIP`
    * `WellFounded`

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

### Tidying

Find duplicate module names.

```
$ for x in $(for x in $(find . -name '*.v') ; do basename -- "$x" ; done | sort | uniq -d) ; do find . -name "$x" ; done
```

Find long lines.

```
$ find . -name '*.v' | xargs grep -n '^.\{80,\}$'
```

Find trailing spaces.

```
$ find . -name '*.v' | xargs grep -n ' \+$'
```

Find double spacing.

```
$ find . -name '*.v' | xargs grep -n '[^ ]  \+'
```

Find loose parentheses.

```
$ find . -name '*.v' | xargs grep -n '\((\|\[\|{\) \| \()\|\]\|}\)'
```

Find loose type signatures.

```
find . -name '*.v' | xargs grep -n '[^ ]:\|:[^ =>]'
```

### Towers of Arithmetic Lemmas

There is this tower of cyclicity lemmas.

```
    cycle_1_0
      f 0 = f 0
    cycle_2_0              cycle_2_1
    f 0 1 = f 0 1          f 0 1 = f 1 0
    cycle_3_0              cycle_3_1              cycle_3_2
  f 0 1 2 = f 0 1 2      f 0 1 2 = f 2 0 1      f 0 1 2 = f 1 2 0
    cycle_4_0              cycle_4_1              cycle_4_2              cycle_4_3
f 0 1 2 3 = f 0 1 2 3  f 0 1 2 3 = f 2 0 1 3  f 0 1 2 3 = f 1 2 0 3  f 0 1 2 3 = f 1 2 3 0
```

The first column is trivial by reflexivity and
every column beyond the second one can be derived from it.
Thus, it is enough to have `cycle_2_1`, `cycle_3_1`, `cycle_4_1`, ... and
we may omit the suffix `_1` from the names.
The number of independent lemmas is `fun n => if n < 2 then 0 else 1`.

```
    cycle_2
    f 0 1 = f 1 0
    cycle_3
  f 0 1 2 = f 2 0 1
    cycle_4
f 0 1 2 3 = f 3 0 1 2
```

There is this tower of commutativity lemmas.

```
     comm_2_0_1
    f 0 1 = f 1 0
     comm_3_0_1             comm_3_0_2                                    comm_3_1_2
  f 0 1 2 = f 1 0 2      f 0 1 2 = f 2 1 0                             f 0 1 2 = f 0 2 1
     comm_4_0_1             comm_4_0_2             comm_4_0_3             comm_4_1_2             comm_4_1_3             comm_4_2_3
f 0 1 2 3 = f 1 0 2 3  f 0 1 2 3 = f 2 1 0 3  f 0 1 2 3 = f 3 1 2 0  f 0 1 2 3 = f 0 2 1 3  f 0 1 2 3 = f 0 3 2 1  f 0 1 2 3 = f 0 1 3 2
```

Every lemma on each row can be derived from the span of the row.
The first row on each column is enough to derive the rest of the column;
the other direction is also true with functional extensionality.
Thus, it is enough to have `comm_2_0_1`, `comm_3_0_2`, `comm_4_0_3`, ... and
we may omit the prefix `_n` from the names.
The number of independent lemmas is `fun n => if n < 2 then 0 else 1`.

```
     comm_0_1
    f 0 1 = f 1 0
     comm_0_2
  f 0 1 2 = f 2 1 0
     comm_0_3
f 0 1 2 3 = f 3 1 2 0
```

With functional extensionality,
we could write the tower differently,
although we still could not realize the limit.

```
     comm_0_1    comm_1_2    comm_2_3
f 0 1 2 3 = f 1 0 2 3 = f 1 2 0 3 = f 1 2 3 0
```

There is this tower of associativity lemmas.

```
              assoc_2_0_1
        f (f 0 1) 2 = f 0 (f 1 2)
              assoc_3_0_1                                assoc_3_0_2                                                                           assoc_3_1_2
    f (f 0 1 2) 3 4 = f 0 (f 1 2 3) 4          f (f 0 1 2) 3 4 = f 0 1 (f 2 3 4)                                                     f 0 (f 1 2 3) 4 = f 0 1 (f 2 3 4)
              assoc_4_0_1                                assoc_4_0_2                                assoc_4_0_3                                assoc_4_1_2                                assoc_4_1_3                                assoc_4_2_3
f (f 0 1 2 3) 4 5 6 = f 0 (f 1 2 3 4) 5 6  f (f 0 1 2 3) 4 5 6 = f 0 1 (f 2 3 4 5) 6  f (f 0 1 2 3) 4 5 6 = f 0 1 2 (f 3 4 5 6)  f 0 (f 1 2 3 4) 5 6 = f 0 1 (f 2 3 4 5) 6  f 0 (f 1 2 3 4) 5 6 = f 0 1 2 (f 3 4 5 6)  f 0 1 (f 2 3 4 5) 6 = f 0 1 2 (f 3 4 5 6)
```

Every lemma on each row can be derived from the span of the row.
Thus, it is enough to have `assoc_2_0_1`, `assoc_3_0_1`, `assoc_3_1_2`,
`assoc_4_0_1`, `assoc_4_1_2`, `assoc_4_2_3`, ... and
we could even omit the suffix `_i` from the names (although we do not,
because that would make the names asymmetric and confusing).
The number of independent lemmas is `fun n => if n < 2 then 0 else n - 1`.

```
                                    assoc_2_0_1
                              f (f 0 1) 2 = f 0 (f 1 2)
                             assoc_3_0_1       assoc_3_1_2
                   f (f 0 1 2) 3 4 = f 0 (f 1 2 3) 4 = f 0 1 (f 2 3 4)
              assoc_4_0_1           assoc_4_1_2           assoc_4_2_3
f (f 0 1 2 3) 4 5 6 = f 0 (f 1 2 3 4) 5 6 = f 0 1 (f 2 3 4 5) 6 = f 0 1 2 (f 3 4 5 6)
```

### Piles of Things to Do

It would be easier to separate algebraic, relational,
functional, order-theoretic, metric, etc properties from each other,
but, alas, they are too intertwined for such a separation to be useful.

Do these things.

* Remove operational type class use from predicative classes
  unless overloading is needed.
* Write Coqdoc documentation comments for each class instead of each module.
* Finish refactoring Coq modules into a flat hierarchy.
* Free modules (with an explicit basis) can now be built.
* Regular semigroups have two equivalent definitions;
  try to implement them as an isomorphism.
* Now that we have one-sorted algebra (abstract algebra)
  generalized to many-sorted algebra (universal algebra) and
  oidified to one-sorted partial algebra (category theory),
  what happens if we go looking for many-sorted partial algebra?
* Had a look at Clifford Algebras and Dirac Operators
  in Harmonic Analysis by Gilbert and Murray; it was terrible.
* Setoid model now.
* Monoidal categories maybe later.

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
    * DEZ has: fn (function), un (unit), unl (unital), invol, absorb
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
From DEZ.Has Require Export
  EquivalenceRelation BinaryOperation Unit UnaryOperation.
From DEZ.Is Require Export
  Proper Monoid ExternallyInvertible.
From DEZ.ShouldHave Require Import
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

## Workflow Things

You can load generated OCaml code as follows.

```
# apt install thrift-compiler
$ pip3 install --user thrift
$ opam install thrift
$ inside plant make
$ inside primate make
$ inside primate utop -I gen-ocaml
utop # #require "thrift" ;;
utop # #mod_use "gen-ocaml/polynomial_types.ml" ;;
utop # #use "broker.ml" ;;
```

Collate all logs together as follows.

```
$ LC_ALL=C sort -nk 1.2 -s primate.log scales.log
```

Run simple gui, server and broker as follows.

```
$ ( sleep 1 && make -C fur -s run ; ) & \
  ( sleep 1 && make -C scales -s run ; ) & \
  ( sleep 1 && make -C spores -s run ; ) & \
  make -C ape -s run
```

It also works without build automation and can be distributed.

```
$ ( sleep 1 && cd fur && ./main 127.0.0.1 8191 ; ) & \
  ( sleep 1 && cd scales && ./main 127.0.0.1 8191 ; ) & \
  ( sleep 1 && cd spores && ./main 127.0.0.1 8191 ; ) & \
  ( cd ape && ./main 8191 ; )
```

Technically, we could unify the command with the following `main` program,
but it would require `bash` to pass its correctly.

```
#! /bin/bash

python3 main.py "$@"
```

Another way is to do the following.

```
#! /usr/bin/env python3

import os
import sys

os.execvp('python3', ['python3', 'main.py'] + sys.argv[1:])
```

In case of `ECONNREFUSED`, the server is probably dead.
Start it again as follows.

```
$ ( cd ape && ./main 8191 ; ) &
```

In case of `ENOTCONN`, the server is probably stuck.
Find and stop it as follows.

```
$ netstat -A inet -p
$ kill 16384
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
